import V185TrunkScan21Chunk164

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_2011725 : List Nat := [1, 6, 1, 1, 2, 1, 3, 2, 4]
def baseStart_2011725 : Nat := 118140960795 + 2011725 * 2 ^ 59
def prefixEnd_2011725 : Nat := 4983230072969 + 3 ^ 40 * 2011725 * 2
def baseEnd_2011725 : Nat := 459103053184998600171445

theorem tailTrace_2011725 : CollatzResearch.WordTrace tailWord_2011725 prefixEnd_2011725 459103053184998600171445 := by
  unfold tailWord_2011725
  simp only [CollatzResearch.WordTrace]
  refine ⟨73373638636871375121684629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48915759091247583414456419 73373638636871375121684629)
  ·
    refine ⟨3439389311103345708828967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 73373638636871375121684629 3439389311103345708828967)
    ·
      refine ⟨5159083966655018563243451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3439389311103345708828967 5159083966655018563243451)
      ·
        refine ⟨7738625949982527844865177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5159083966655018563243451 7738625949982527844865177)
        ·
          refine ⟨5803969462486895883648883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7738625949982527844865177 5803969462486895883648883)
          ·
            refine ⟨8705954193730343825473325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5803969462486895883648883 8705954193730343825473325)
            ·
              refine ⟨3264732822648878934552497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8705954193730343825473325 3264732822648878934552497)
              ·
                refine ⟨2448549616986659200914373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3264732822648878934552497 2448549616986659200914373)
                ·
                  refine ⟨459103053184998600171445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2448549616986659200914373 459103053184998600171445)
                  ·
                    rfl

theorem cell21_2011725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 3, 2, 4].length) (baseStart_2011725 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2011725 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2011725 prefixEnd_2011725 := by exact prefixLift 2011725
  have htrace : WordTrace (prefixWord ++ tailWord_2011725) baseStart_2011725 baseEnd_2011725 := by
    simpa [prefixWord, tailWord_2011725, baseEnd_2011725] using wordTrace_append hprefix tailTrace_2011725
  have hstable : (prefixWord ++ tailWord_2011725).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2011725).length < 2 ^ (prefixWord ++ tailWord_2011725).sum := by decide
  have hdescent : baseEnd_2011725 < baseStart_2011725 := by decide
  rcases family_descends (prefixWord ++ tailWord_2011725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2011736 : List Nat := [2, 1, 2, 2, 1, 2, 3, 3, 5]
def baseStart_2011736 : Nat := 118140960795 + 2011736 * 2 ^ 59
def prefixEnd_2011736 : Nat := 4983230072969 + 3 ^ 40 * 2011736 * 2
def baseEnd_2011736 : Nat := 459105563534865025488089

theorem tailTrace_2011736 : CollatzResearch.WordTrace tailWord_2011736 prefixEnd_2011736 459105563534865025488089 := by
  unfold tailWord_2011736
  simp only [CollatzResearch.WordTrace]
  refine ⟨36687019919915762000167531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48916026559887682666890041 36687019919915762000167531)
  ·
    refine ⟨55030529879873643000251297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36687019919915762000167531 55030529879873643000251297)
    ·
      refine ⟨41272897409905232250188473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55030529879873643000251297 41272897409905232250188473)
      ·
        refine ⟨30954673057428924187641355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41272897409905232250188473 30954673057428924187641355)
        ·
          refine ⟨46432009586143386281462033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30954673057428924187641355 46432009586143386281462033)
          ·
            refine ⟨34824007189607539711096525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46432009586143386281462033 34824007189607539711096525)
            ·
              refine ⟨13059002696102827391661197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34824007189607539711096525 13059002696102827391661197)
              ·
                refine ⟨4897126011038560271872949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13059002696102827391661197 4897126011038560271872949)
                ·
                  refine ⟨459105563534865025488089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4897126011038560271872949 459105563534865025488089)
                  ·
                    rfl

theorem cell21_2011736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 3, 5].length) (baseStart_2011736 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2011736 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2011736 prefixEnd_2011736 := by exact prefixLift 2011736
  have htrace : WordTrace (prefixWord ++ tailWord_2011736) baseStart_2011736 baseEnd_2011736 := by
    simpa [prefixWord, tailWord_2011736, baseEnd_2011736] using wordTrace_append hprefix tailTrace_2011736
  have hstable : (prefixWord ++ tailWord_2011736).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2011736).length < 2 ^ (prefixWord ++ tailWord_2011736).sum := by decide
  have hdescent : baseEnd_2011736 < baseStart_2011736 := by decide
  rcases family_descends (prefixWord ++ tailWord_2011736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2011781 : List Nat := [1, 3, 1, 1, 4, 2, 9]
def baseStart_2011781 : Nat := 118140960795 + 2011781 * 2 ^ 59
def prefixEnd_2011781 : Nat := 4983230072969 + 3 ^ 40 * 2011781 * 2
def baseEnd_2011781 : Nat := 51012870349772771915333

theorem tailTrace_2011781 : CollatzResearch.WordTrace tailWord_2011781 prefixEnd_2011781 51012870349772771915333 := by
  unfold tailWord_2011781
  simp only [CollatzResearch.WordTrace]
  refine ⟨73375681124668496685723197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48917120749778997790482131 73375681124668496685723197)
  ·
    refine ⟨27515880421750686257146199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73375681124668496685723197 27515880421750686257146199)
    ·
      refine ⟨41273820632626029385719299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27515880421750686257146199 41273820632626029385719299)
      ·
        refine ⟨61910730948939044078578949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41273820632626029385719299 61910730948939044078578949)
        ·
          refine ⟨11608262052926070764733553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61910730948939044078578949 11608262052926070764733553)
          ·
            refine ⟨8706196539694553073550165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11608262052926070764733553 8706196539694553073550165)
            ·
              refine ⟨51012870349772771915333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8706196539694553073550165 51012870349772771915333)
              ·
                rfl

theorem cell21_2011781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 9].length) (baseStart_2011781 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2011781 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2011781 prefixEnd_2011781 := by exact prefixLift 2011781
  have htrace : WordTrace (prefixWord ++ tailWord_2011781) baseStart_2011781 baseEnd_2011781 := by
    simpa [prefixWord, tailWord_2011781, baseEnd_2011781] using wordTrace_append hprefix tailTrace_2011781
  have hstable : (prefixWord ++ tailWord_2011781).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2011781).length < 2 ^ (prefixWord ++ tailWord_2011781).sum := by decide
  have hdescent : baseEnd_2011781 < baseStart_2011781 := by decide
  rcases family_descends (prefixWord ++ tailWord_2011781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2011812 : List Nat := [2, 3, 1, 2, 2, 1, 2, 1, 7]
def baseStart_2011812 : Nat := 118140960795 + 2011812 * 2 ^ 59
def prefixEnd_2011812 : Nat := 4983230072969 + 3 ^ 40 * 2011812 * 2
def baseEnd_2011812 : Nat := 459122907770305782221267

theorem tailTrace_2011812 : CollatzResearch.WordTrace tailWord_2011812 prefixEnd_2011812 459122907770305782221267 := by
  unfold tailWord_2011812
  simp only [CollatzResearch.WordTrace]
  refine ⟨36688405893778094490050845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48917874525037459320067793 36688405893778094490050845)
  ·
    refine ⟨13758152210166785433769067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36688405893778094490050845 13758152210166785433769067)
    ·
      refine ⟨20637228315250178150653601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13758152210166785433769067 20637228315250178150653601)
      ·
        refine ⟨15477921236437633612990201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20637228315250178150653601 15477921236437633612990201)
        ·
          refine ⟨11608440927328225209742651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15477921236437633612990201 11608440927328225209742651)
          ·
            refine ⟨17412661390992337814613977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11608440927328225209742651 17412661390992337814613977)
            ·
              refine ⟨13059496043244253360960483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17412661390992337814613977 13059496043244253360960483)
              ·
                refine ⟨19589244064866380041440725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13059496043244253360960483 19589244064866380041440725)
                ·
                  refine ⟨459122907770305782221267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19589244064866380041440725 459122907770305782221267)
                  ·
                    rfl

theorem cell21_2011812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 1, 7].length) (baseStart_2011812 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2011812 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2011812 prefixEnd_2011812 := by exact prefixLift 2011812
  have htrace : WordTrace (prefixWord ++ tailWord_2011812) baseStart_2011812 baseEnd_2011812 := by
    simpa [prefixWord, tailWord_2011812, baseEnd_2011812] using wordTrace_append hprefix tailTrace_2011812
  have hstable : (prefixWord ++ tailWord_2011812).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2011812).length < 2 ^ (prefixWord ++ tailWord_2011812).sum := by decide
  have hdescent : baseEnd_2011812 < baseStart_2011812 := by decide
  rcases family_descends (prefixWord ++ tailWord_2011812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2011947 : List Nat := [1, 1, 1, 1, 2, 1, 2, 3, 9]
def baseStart_2011947 : Nat := 118140960795 + 2011947 * 2 ^ 59
def prefixEnd_2011947 : Nat := 4983230072969 + 3 ^ 40 * 2011947 * 2
def baseEnd_2011947 : Nat := 459153716609575547470991

theorem tailTrace_2011947 : CollatzResearch.WordTrace tailWord_2011947 prefixEnd_2011947 459153716609575547470991 := by
  unfold tailWord_2011947
  simp only [CollatzResearch.WordTrace]
  refine ⟨73381735642067107036266095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48921157094711404690844063 73381735642067107036266095)
  ·
    refine ⟨110072603463100660554399143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73381735642067107036266095 110072603463100660554399143)
    ·
      refine ⟨165108905194650990831598715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110072603463100660554399143 165108905194650990831598715)
      ·
        refine ⟨247663357791976486247398073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165108905194650990831598715 247663357791976486247398073)
        ·
          refine ⟨185747518343982364685548555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 247663357791976486247398073 185747518343982364685548555)
          ·
            refine ⟨278621277515973547028322833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185747518343982364685548555 278621277515973547028322833)
            ·
              refine ⟨208965958136980160271242125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 278621277515973547028322833 208965958136980160271242125)
              ·
                refine ⟨78362234301367560101715797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 208965958136980160271242125 78362234301367560101715797)
                ·
                  refine ⟨459153716609575547470991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 78362234301367560101715797 459153716609575547470991)
                  ·
                    rfl

theorem cell21_2011947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 3, 9].length) (baseStart_2011947 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2011947 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2011947 prefixEnd_2011947 := by exact prefixLift 2011947
  have htrace : WordTrace (prefixWord ++ tailWord_2011947) baseStart_2011947 baseEnd_2011947 := by
    simpa [prefixWord, tailWord_2011947, baseEnd_2011947] using wordTrace_append hprefix tailTrace_2011947
  have hstable : (prefixWord ++ tailWord_2011947).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2011947).length < 2 ^ (prefixWord ++ tailWord_2011947).sum := by decide
  have hdescent : baseEnd_2011947 < baseStart_2011947 := by decide
  rcases family_descends (prefixWord ++ tailWord_2011947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2011950 : List Nat := [4, 1, 3, 2, 1, 1, 9]
def baseStart_2011950 : Nat := 118140960795 + 2011950 * 2 ^ 59
def prefixEnd_2011950 : Nat := 4983230072969 + 3 ^ 40 * 2011950 * 2
def baseEnd_2011950 : Nat := 51017155694494245435665

theorem tailTrace_2011950 : CollatzResearch.WordTrace tailWord_2011950 prefixEnd_2011950 51017155694494245435665 := by
  unfold tailWord_2011950
  simp only [CollatzResearch.WordTrace]
  refine ⟨9172730632632029818578163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48921230040704159032416869 9172730632632029818578163)
  ·
    refine ⟨13759095948948044727867245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9172730632632029818578163 13759095948948044727867245)
    ·
      refine ⟨5159660980855516772950217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13759095948948044727867245 5159660980855516772950217)
      ·
        refine ⟨3869745735641637579712663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5159660980855516772950217 3869745735641637579712663)
        ·
          refine ⟨5804618603462456369568995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3869745735641637579712663 5804618603462456369568995)
          ·
            refine ⟨8706927905193684554353493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5804618603462456369568995 8706927905193684554353493)
            ·
              refine ⟨51017155694494245435665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8706927905193684554353493 51017155694494245435665)
              ·
                rfl

theorem cell21_2011950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 9].length) (baseStart_2011950 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2011950 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2011950 prefixEnd_2011950 := by exact prefixLift 2011950
  have htrace : WordTrace (prefixWord ++ tailWord_2011950) baseStart_2011950 baseEnd_2011950 := by
    simpa [prefixWord, tailWord_2011950, baseEnd_2011950] using wordTrace_append hprefix tailTrace_2011950
  have hstable : (prefixWord ++ tailWord_2011950).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2011950).length < 2 ^ (prefixWord ++ tailWord_2011950).sum := by decide
  have hdescent : baseEnd_2011950 < baseStart_2011950 := by decide
  rcases family_descends (prefixWord ++ tailWord_2011950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2011956 : List Nat := [2, 5, 1, 1, 3, 1, 3, 2, 3]
def baseStart_2011956 : Nat := 118140960795 + 2011956 * 2 ^ 59
def prefixEnd_2011956 : Nat := 4983230072969 + 3 ^ 40 * 2011956 * 2
def baseEnd_2011956 : Nat := 459155770532193531820973

theorem tailTrace_2011956 : CollatzResearch.WordTrace tailWord_2011956 prefixEnd_2011956 459155770532193531820973 := by
  unfold tailWord_2011956
  simp only [CollatzResearch.WordTrace]
  refine ⟨36691031949517250786671861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48921375932689667715562481 36691031949517250786671861)
  ·
    refine ⟨3439784245267242261250487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 36691031949517250786671861 3439784245267242261250487)
    ·
      refine ⟨5159676367900863391875731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3439784245267242261250487 5159676367900863391875731)
      ·
        refine ⟨7739514551851295087813597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5159676367900863391875731 7739514551851295087813597)
        ·
          refine ⟨2902317956944235657930099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7739514551851295087813597 2902317956944235657930099)
          ·
            refine ⟨4353476935416353486895149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2902317956944235657930099 4353476935416353486895149)
            ·
              refine ⟨1632553850781132557585681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4353476935416353486895149 1632553850781132557585681)
              ·
                refine ⟨1224415388085849418189261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1632553850781132557585681 1224415388085849418189261)
                ·
                  refine ⟨459155770532193531820973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1224415388085849418189261 459155770532193531820973)
                  ·
                    rfl

theorem cell21_2011956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 3, 2, 3].length) (baseStart_2011956 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2011956 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2011956 prefixEnd_2011956 := by exact prefixLift 2011956
  have htrace : WordTrace (prefixWord ++ tailWord_2011956) baseStart_2011956 baseEnd_2011956 := by
    simpa [prefixWord, tailWord_2011956, baseEnd_2011956] using wordTrace_append hprefix tailTrace_2011956
  have hstable : (prefixWord ++ tailWord_2011956).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2011956).length < 2 ^ (prefixWord ++ tailWord_2011956).sum := by decide
  have hdescent : baseEnd_2011956 < baseStart_2011956 := by decide
  rcases family_descends (prefixWord ++ tailWord_2011956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2011978 : List Nat := [3, 1, 2, 1, 1, 1, 2, 2, 8]
def baseStart_2011978 : Nat := 118140960795 + 2011978 * 2 ^ 59
def prefixEnd_2011978 : Nat := 4983230072969 + 3 ^ 40 * 2011978 * 2
def baseEnd_2011978 : Nat := 459160791231926382454261

theorem tailTrace_2011978 : CollatzResearch.WordTrace tailWord_2011978 prefixEnd_2011978 459160791231926382454261 := by
  unfold tailWord_2011978
  simp only [CollatzResearch.WordTrace]
  refine ⟨18345716576238699832661147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48921910869969866220429725 18345716576238699832661147)
  ·
    refine ⟨27518574864358049748991721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18345716576238699832661147 27518574864358049748991721)
    ·
      refine ⟨20638931148268537311743791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27518574864358049748991721 20638931148268537311743791)
      ·
        refine ⟨30958396722402805967615687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20638931148268537311743791 30958396722402805967615687)
        ·
          refine ⟨46437595083604208951423531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30958396722402805967615687 46437595083604208951423531)
          ·
            refine ⟨69656392625406313427135297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46437595083604208951423531 69656392625406313427135297)
            ·
              refine ⟨52242294469054735070351473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69656392625406313427135297 52242294469054735070351473)
              ·
                refine ⟨39181720851791051302763605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52242294469054735070351473 39181720851791051302763605)
                ·
                  refine ⟨459160791231926382454261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39181720851791051302763605 459160791231926382454261)
                  ·
                    rfl

theorem cell21_2011978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 2, 8].length) (baseStart_2011978 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2011978 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2011978 prefixEnd_2011978 := by exact prefixLift 2011978
  have htrace : WordTrace (prefixWord ++ tailWord_2011978) baseStart_2011978 baseEnd_2011978 := by
    simpa [prefixWord, tailWord_2011978, baseEnd_2011978] using wordTrace_append hprefix tailTrace_2011978
  have hstable : (prefixWord ++ tailWord_2011978).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2011978).length < 2 ^ (prefixWord ++ tailWord_2011978).sum := by decide
  have hdescent : baseEnd_2011978 < baseStart_2011978 := by decide
  rcases family_descends (prefixWord ++ tailWord_2011978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2012023 : List Nat := [1, 1, 3, 1, 1, 2, 1, 2, 9]
def baseStart_2012023 : Nat := 118140960795 + 2012023 * 2 ^ 59
def prefixEnd_2012023 : Nat := 4983230072969 + 3 ^ 40 * 2012023 * 2
def baseEnd_2012023 : Nat := 459171060845016304204169

theorem tailTrace_2012023 : CollatzResearch.WordTrace tailWord_2012023 prefixEnd_2012023 459171060845016304204169 := by
  unfold tailWord_2012023
  simp only [CollatzResearch.WordTrace]
  refine ⟨73384507589791772016032723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48923005059861181344021815 73384507589791772016032723)
  ·
    refine ⟨110076761384687658024049085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73384507589791772016032723 110076761384687658024049085)
    ·
      refine ⟨41278785519257871759018407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110076761384687658024049085 41278785519257871759018407)
      ·
        refine ⟨61918178278886807638527611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41278785519257871759018407 61918178278886807638527611)
        ·
          refine ⟨92877267418330211457791417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61918178278886807638527611 92877267418330211457791417)
          ·
            refine ⟨69657950563747658593343563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92877267418330211457791417 69657950563747658593343563)
            ·
              refine ⟨104486925845621487890015345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69657950563747658593343563 104486925845621487890015345)
              ·
                refine ⟨78365194384216115917511509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104486925845621487890015345 78365194384216115917511509)
                ·
                  refine ⟨459171060845016304204169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 78365194384216115917511509 459171060845016304204169)
                  ·
                    rfl

theorem cell21_2012023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 2, 9].length) (baseStart_2012023 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2012023 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2012023 prefixEnd_2012023 := by exact prefixLift 2012023
  have htrace : WordTrace (prefixWord ++ tailWord_2012023) baseStart_2012023 baseEnd_2012023 := by
    simpa [prefixWord, tailWord_2012023, baseEnd_2012023] using wordTrace_append hprefix tailTrace_2012023
  have hstable : (prefixWord ++ tailWord_2012023).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2012023).length < 2 ^ (prefixWord ++ tailWord_2012023).sum := by decide
  have hdescent : baseEnd_2012023 < baseStart_2012023 := by decide
  rcases family_descends (prefixWord ++ tailWord_2012023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2012040 : List Nat := [2, 1, 3, 3, 2, 1, 1, 1, 7]
def baseStart_2012040 : Nat := 118140960795 + 2012040 * 2 ^ 59
def prefixEnd_2012040 : Nat := 4983230072969 + 3 ^ 40 * 2012040 * 2
def baseEnd_2012040 : Nat := 459174940476628052420801

theorem tailTrace_2012040 : CollatzResearch.WordTrace tailWord_2012040 prefixEnd_2012040 459174940476628052420801 := by
  unfold tailWord_2012040
  simp only [CollatzResearch.WordTrace]
  refine ⟨36692563815365091959700787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48923418420486789279601049 36692563815365091959700787)
  ·
    refine ⟨55038845723047637939551181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36692563815365091959700787 55038845723047637939551181)
    ·
      refine ⟨20639567146142864227331693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55038845723047637939551181 20639567146142864227331693)
      ·
        refine ⟨7739837679803574085249385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20639567146142864227331693 7739837679803574085249385)
        ·
          refine ⟨5804878259852680563937039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7739837679803574085249385 5804878259852680563937039)
          ·
            refine ⟨8707317389779020845905559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5804878259852680563937039 8707317389779020845905559)
            ·
              refine ⟨13060976084668531268858339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8707317389779020845905559 13060976084668531268858339)
              ·
                refine ⟨19591464127002796903287509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13060976084668531268858339 19591464127002796903287509)
                ·
                  refine ⟨459174940476628052420801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19591464127002796903287509 459174940476628052420801)
                  ·
                    rfl

theorem cell21_2012040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 1, 7].length) (baseStart_2012040 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2012040 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2012040 prefixEnd_2012040 := by exact prefixLift 2012040
  have htrace : WordTrace (prefixWord ++ tailWord_2012040) baseStart_2012040 baseEnd_2012040 := by
    simpa [prefixWord, tailWord_2012040, baseEnd_2012040] using wordTrace_append hprefix tailTrace_2012040
  have hstable : (prefixWord ++ tailWord_2012040).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2012040).length < 2 ^ (prefixWord ++ tailWord_2012040).sum := by decide
  have hdescent : baseEnd_2012040 < baseStart_2012040 := by decide
  rcases family_descends (prefixWord ++ tailWord_2012040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2012085 : List Nat := [1, 3, 3, 2, 1, 1, 2, 8]
def baseStart_2012085 : Nat := 118140960795 + 2012085 * 2 ^ 59
def prefixEnd_2012085 : Nat := 4983230072969 + 3 ^ 40 * 2012085 * 2
def baseEnd_2012085 : Nat := 153061736696572658056903

theorem tailTrace_2012085 : CollatzResearch.WordTrace tailWord_2012085 prefixEnd_2012085 153061736696572658056903 := by
  unfold tailWord_2012085
  simp only [CollatzResearch.WordTrace]
  refine ⟨73386768915567156604789709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48924512610378104403193139 73386768915567156604789709)
  ·
    refine ⟨27520038343337683726796141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73386768915567156604789709 27520038343337683726796141)
    ·
      refine ⟨10320014378751631397548553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27520038343337683726796141 10320014378751631397548553)
      ·
        refine ⟨7740010784063723548161415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10320014378751631397548553 7740010784063723548161415)
        ·
          refine ⟨11610016176095585322242123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7740010784063723548161415 11610016176095585322242123)
          ·
            refine ⟨17415024264143377983363185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11610016176095585322242123 17415024264143377983363185)
            ·
              refine ⟨13061268198107533487522389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17415024264143377983363185 13061268198107533487522389)
              ·
                refine ⟨153061736696572658056903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13061268198107533487522389 153061736696572658056903)
                ·
                  rfl

theorem cell21_2012085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 8].length) (baseStart_2012085 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2012085 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2012085 prefixEnd_2012085 := by exact prefixLift 2012085
  have htrace : WordTrace (prefixWord ++ tailWord_2012085) baseStart_2012085 baseEnd_2012085 := by
    simpa [prefixWord, tailWord_2012085, baseEnd_2012085] using wordTrace_append hprefix tailTrace_2012085
  have hstable : (prefixWord ++ tailWord_2012085).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2012085).length < 2 ^ (prefixWord ++ tailWord_2012085).sum := by decide
  have hdescent : baseEnd_2012085 < baseStart_2012085 := by decide
  rcases family_descends (prefixWord ++ tailWord_2012085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2012088 : List Nat := [2, 1, 2, 1, 2, 5, 3, 1, 4]
def baseStart_2012088 : Nat := 118140960795 + 2012088 * 2 ^ 59
def prefixEnd_2012088 : Nat := 4983230072969 + 3 ^ 40 * 2012088 * 2
def baseEnd_2012088 : Nat := 459185894730590635620703

theorem tailTrace_2012088 : CollatzResearch.WordTrace tailWord_2012088 prefixEnd_2012088 459185894730590635620703 := by
  unfold tailWord_2012088
  simp only [CollatzResearch.WordTrace]
  refine ⟨36693439167278144058574459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48924585556370858744765945 36693439167278144058574459)
  ·
    refine ⟨55040158750917216087861689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36693439167278144058574459 55040158750917216087861689)
    ·
      refine ⟨41280119063187912065896267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55040158750917216087861689 41280119063187912065896267)
      ·
        refine ⟨61920178594781868098844401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41280119063187912065896267 61920178594781868098844401)
        ·
          refine ⟨46440133946086401074133301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61920178594781868098844401 46440133946086401074133301)
          ·
            refine ⟨4353762557445600100699997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 46440133946086401074133301 4353762557445600100699997)
            ·
              refine ⟨1632660959042100037762499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4353762557445600100699997 1632660959042100037762499)
              ·
                refine ⟨2448991438563150056643749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1632660959042100037762499 2448991438563150056643749)
                ·
                  refine ⟨459185894730590635620703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2448991438563150056643749 459185894730590635620703)
                  ·
                    rfl

theorem cell21_2012088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 3, 1, 4].length) (baseStart_2012088 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2012088 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2012088 prefixEnd_2012088 := by exact prefixLift 2012088
  have htrace : WordTrace (prefixWord ++ tailWord_2012088) baseStart_2012088 baseEnd_2012088 := by
    simpa [prefixWord, tailWord_2012088, baseEnd_2012088] using wordTrace_append hprefix tailTrace_2012088
  have hstable : (prefixWord ++ tailWord_2012088).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2012088).length < 2 ^ (prefixWord ++ tailWord_2012088).sum := by decide
  have hdescent : baseEnd_2012088 < baseStart_2012088 := by decide
  rcases family_descends (prefixWord ++ tailWord_2012088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2012161 : List Nat := [1, 2, 4, 1, 2, 2, 2, 7]
def baseStart_2012161 : Nat := 118140960795 + 2012161 * 2 ^ 59
def prefixEnd_2012161 : Nat := 4983230072969 + 3 ^ 40 * 2012161 * 2
def baseEnd_2012161 : Nat := 153067518108386243634629

theorem tailTrace_2012161 : CollatzResearch.WordTrace tailWord_2012161 prefixEnd_2012161 153067518108386243634629 := by
  unfold tailWord_2012161
  simp only [CollatzResearch.WordTrace]
  refine ⟨73389540863291821584556337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48926360575527881056370891 73389540863291821584556337)
  ·
    refine ⟨55042155647468866188417253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73389540863291821584556337 55042155647468866188417253)
    ·
      refine ⟨10320404183900412410328235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55042155647468866188417253 10320404183900412410328235)
      ·
        refine ⟨15480606275850618615492353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10320404183900412410328235 15480606275850618615492353)
        ·
          refine ⟨11610454706887963961619265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15480606275850618615492353 11610454706887963961619265)
          ·
            refine ⟨8707841030165972971214449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11610454706887963961619265 8707841030165972971214449)
            ·
              refine ⟨6530880772624479728410837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8707841030165972971214449 6530880772624479728410837)
              ·
                refine ⟨153067518108386243634629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6530880772624479728410837 153067518108386243634629)
                ·
                  rfl

theorem cell21_2012161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 2, 7].length) (baseStart_2012161 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2012161 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2012161 prefixEnd_2012161 := by exact prefixLift 2012161
  have htrace : WordTrace (prefixWord ++ tailWord_2012161) baseStart_2012161 baseEnd_2012161 := by
    simpa [prefixWord, tailWord_2012161, baseEnd_2012161] using wordTrace_append hprefix tailTrace_2012161
  have hstable : (prefixWord ++ tailWord_2012161).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2012161).length < 2 ^ (prefixWord ++ tailWord_2012161).sum := by decide
  have hdescent : baseEnd_2012161 < baseStart_2012161 := by decide
  rcases family_descends (prefixWord ++ tailWord_2012161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2012316 : List Nat := [2, 2, 3, 2, 1, 2, 4, 1, 4]
def baseStart_2012316 : Nat := 118140960795 + 2012316 * 2 ^ 59
def prefixEnd_2012316 : Nat := 4983230072969 + 3 ^ 40 * 2012316 * 2
def baseEnd_2012316 : Nat := 459237927436912905820237

theorem tailTrace_2012316 : CollatzResearch.WordTrace tailWord_2012316 prefixEnd_2012316 459237927436912905820237 := by
  unfold tailWord_2012316
  simp only [CollatzResearch.WordTrace]
  refine ⟨36697597088865141528224401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48930129451820188704299201 36697597088865141528224401)
  ·
    refine ⟨27523197816648856146168301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36697597088865141528224401 27523197816648856146168301)
    ·
      refine ⟨10321199181243321054813113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27523197816648856146168301 10321199181243321054813113)
      ·
        refine ⟨7740899385932490791109835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10321199181243321054813113 7740899385932490791109835)
        ·
          refine ⟨11611349078898736186664753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7740899385932490791109835 11611349078898736186664753)
          ·
            refine ⟨8708511809174052139998565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11611349078898736186664753 8708511809174052139998565)
            ·
              refine ⟨1632845964220134776249731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8708511809174052139998565 1632845964220134776249731)
              ·
                refine ⟨2449268946330202164374597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1632845964220134776249731 2449268946330202164374597)
                ·
                  refine ⟨459237927436912905820237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2449268946330202164374597 459237927436912905820237)
                  ·
                    rfl

theorem cell21_2012316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 4, 1, 4].length) (baseStart_2012316 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2012316 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2012316 prefixEnd_2012316 := by exact prefixLift 2012316
  have htrace : WordTrace (prefixWord ++ tailWord_2012316) baseStart_2012316 baseEnd_2012316 := by
    simpa [prefixWord, tailWord_2012316, baseEnd_2012316] using wordTrace_append hprefix tailTrace_2012316
  have hstable : (prefixWord ++ tailWord_2012316).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2012316).length < 2 ^ (prefixWord ++ tailWord_2012316).sum := by decide
  have hdescent : baseEnd_2012316 < baseStart_2012316 := by decide
  rcases family_descends (prefixWord ++ tailWord_2012316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2012330 : List Nat := [3, 1, 5, 1, 1, 1, 2, 7]
def baseStart_2012330 : Nat := 118140960795 + 2012330 * 2 ^ 59
def prefixEnd_2012330 : Nat := 4983230072969 + 3 ^ 40 * 2012330 * 2
def baseEnd_2012330 : Nat := 153080374142550664195625

theorem tailTrace_2012330 : CollatzResearch.WordTrace tailWord_2012330 prefixEnd_2012330 153080374142550664195625 := by
  unfold tailWord_2012330
  simp only [CollatzResearch.WordTrace]
  refine ⟨18348926199919890861864611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48930469866453042298305629 18348926199919890861864611)
  ·
    refine ⟨27523389299879836292796917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18348926199919890861864611 27523389299879836292796917)
    ·
      refine ⟨2580317746863734652449711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 27523389299879836292796917 2580317746863734652449711)
      ·
        refine ⟨3870476620295601978674567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2580317746863734652449711 3870476620295601978674567)
        ·
          refine ⟨5805714930443402968011851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3870476620295601978674567 5805714930443402968011851)
          ·
            refine ⟨8708572395665104452017777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5805714930443402968011851 8708572395665104452017777)
            ·
              refine ⟨6531429296748828339013333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8708572395665104452017777 6531429296748828339013333)
              ·
                refine ⟨153080374142550664195625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6531429296748828339013333 153080374142550664195625)
                ·
                  rfl

theorem cell21_2012330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 2, 7].length) (baseStart_2012330 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2012330 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2012330 prefixEnd_2012330 := by exact prefixLift 2012330
  have htrace : WordTrace (prefixWord ++ tailWord_2012330) baseStart_2012330 baseEnd_2012330 := by
    simpa [prefixWord, tailWord_2012330, baseEnd_2012330] using wordTrace_append hprefix tailTrace_2012330
  have hstable : (prefixWord ++ tailWord_2012330).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2012330).length < 2 ^ (prefixWord ++ tailWord_2012330).sum := by decide
  have hdescent : baseEnd_2012330 < baseStart_2012330 := by decide
  rcases family_descends (prefixWord ++ tailWord_2012330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2012420 : List Nat := [2, 3, 2, 2, 2, 1, 1, 3, 5]
def baseStart_2012420 : Nat := 118140960795 + 2012420 * 2 ^ 59
def prefixEnd_2012420 : Nat := 4983230072969 + 3 ^ 40 * 2012420 * 2
def baseEnd_2012420 : Nat := 459261661653831836086691

theorem tailTrace_2012420 : CollatzResearch.WordTrace tailWord_2012420 prefixEnd_2012420 459261661653831836086691 := by
  unfold tailWord_2012420
  simp only [CollatzResearch.WordTrace]
  refine ⟨36699493684676754409117357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48932658246235672545489809 36699493684676754409117357)
  ·
    refine ⟨13762310131753782903419009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36699493684676754409117357 13762310131753782903419009)
    ·
      refine ⟨10321732598815337177564257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13762310131753782903419009 10321732598815337177564257)
      ·
        refine ⟨7741299449111502883173193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10321732598815337177564257 7741299449111502883173193)
        ·
          refine ⟨5805974586833627162379895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7741299449111502883173193 5805974586833627162379895)
          ·
            refine ⟨8708961880250440743569843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5805974586833627162379895 8708961880250440743569843)
            ·
              refine ⟨13063442820375661115354765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8708961880250440743569843 13063442820375661115354765)
              ·
                refine ⟨4898791057640872918258037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13063442820375661115354765 4898791057640872918258037)
                ·
                  refine ⟨459261661653831836086691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4898791057640872918258037 459261661653831836086691)
                  ·
                    rfl

theorem cell21_2012420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 3, 5].length) (baseStart_2012420 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2012420 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2012420 prefixEnd_2012420 := by exact prefixLift 2012420
  have htrace : WordTrace (prefixWord ++ tailWord_2012420) baseStart_2012420 baseEnd_2012420 := by
    simpa [prefixWord, tailWord_2012420, baseEnd_2012420] using wordTrace_append hprefix tailTrace_2012420
  have hstable : (prefixWord ++ tailWord_2012420).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2012420).length < 2 ^ (prefixWord ++ tailWord_2012420).sum := by decide
  have hdescent : baseEnd_2012420 < baseStart_2012420 := by decide
  rcases family_descends (prefixWord ++ tailWord_2012420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2012465 : List Nat := [1, 2, 2, 3, 3, 3, 7]
def baseStart_2012465 : Nat := 118140960795 + 2012465 * 2 ^ 59
def prefixEnd_2012465 : Nat := 4983230072969 + 3 ^ 40 * 2012465 * 2
def baseEnd_2012465 : Nat := 51030214585213528648511

theorem tailTrace_2012465 : CollatzResearch.WordTrace tailWord_2012465 prefixEnd_2012465 51030214585213528648511 := by
  unfold tailWord_2012465
  simp only [CollatzResearch.WordTrace]
  refine ⟨73400628654190481503622849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48933752436126987669081899 73400628654190481503622849)
  ·
    refine ⟨55050471490642861127717137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73400628654190481503622849 55050471490642861127717137)
    ·
      refine ⟨41287853617982145845787853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55050471490642861127717137 41287853617982145845787853)
      ·
        refine ⟨15482945106743304692170445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41287853617982145845787853 15482945106743304692170445)
        ·
          refine ⟨5806104415028739259563917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15482945106743304692170445 5806104415028739259563917)
          ·
            refine ⟨2177289155635777222336469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5806104415028739259563917 2177289155635777222336469)
            ·
              refine ⟨51030214585213528648511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2177289155635777222336469 51030214585213528648511)
              ·
                rfl

theorem cell21_2012465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 7].length) (baseStart_2012465 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2012465 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2012465 prefixEnd_2012465 := by exact prefixLift 2012465
  have htrace : WordTrace (prefixWord ++ tailWord_2012465) baseStart_2012465 baseEnd_2012465 := by
    simpa [prefixWord, tailWord_2012465, baseEnd_2012465] using wordTrace_append hprefix tailTrace_2012465
  have hstable : (prefixWord ++ tailWord_2012465).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2012465).length < 2 ^ (prefixWord ++ tailWord_2012465).sum := by decide
  have hdescent : baseEnd_2012465 < baseStart_2012465 := by decide
  rcases family_descends (prefixWord ++ tailWord_2012465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2012524 : List Nat := [2, 2, 1, 1, 5, 10]
def baseStart_2012524 : Nat := 118140960795 + 2012524 * 2 ^ 59
def prefixEnd_2012524 : Nat := 4983230072969 + 3 ^ 40 * 2012524 * 2
def baseEnd_2012524 : Nat := 17010570217435213568635

theorem tailTrace_2012524 : CollatzResearch.WordTrace tailWord_2012524 prefixEnd_2012524 17010570217435213568635 := by
  unfold tailWord_2012524
  simp only [CollatzResearch.WordTrace]
  refine ⟨36701390280488367290010313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48935187040651156386680417 36701390280488367290010313)
  ·
    refine ⟨27526042710366275467507735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36701390280488367290010313 27526042710366275467507735)
    ·
      refine ⟨41289064065549413201261603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27526042710366275467507735 41289064065549413201261603)
      ·
        refine ⟨61933596098324119801892405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41289064065549413201261603 61933596098324119801892405)
        ·
          refine ⟨5806274634217886231427413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 61933596098324119801892405 5806274634217886231427413)
          ·
            refine ⟨17010570217435213568635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5806274634217886231427413 17010570217435213568635)
            ·
              rfl

theorem cell21_2012524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 10].length) (baseStart_2012524 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2012524 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2012524 prefixEnd_2012524 := by exact prefixLift 2012524
  have htrace : WordTrace (prefixWord ++ tailWord_2012524) baseStart_2012524 baseEnd_2012524 := by
    simpa [prefixWord, tailWord_2012524, baseEnd_2012524] using wordTrace_append hprefix tailTrace_2012524
  have hstable : (prefixWord ++ tailWord_2012524).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2012524).length < 2 ^ (prefixWord ++ tailWord_2012524).sum := by decide
  have hdescent : baseEnd_2012524 < baseStart_2012524 := by decide
  rcases family_descends (prefixWord ++ tailWord_2012524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2012555 : List Nat := [1, 1, 1, 1, 4, 3, 3, 2, 5]
def baseStart_2012555 : Nat := 118140960795 + 2012555 * 2 ^ 59
def prefixEnd_2012555 : Nat := 4983230072969 + 3 ^ 40 * 2012555 * 2
def baseEnd_2012555 : Nat := 459292470493101601336415

theorem tailTrace_2012555 : CollatzResearch.WordTrace tailWord_2012555 prefixEnd_2012555 459292470493101601336415 := by
  unfold tailWord_2012555
  simp only [CollatzResearch.WordTrace]
  refine ⟨73403911223864426874399119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48935940815909617916266079 73403911223864426874399119)
  ·
    refine ⟨110105866835796640311598679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73403911223864426874399119 110105866835796640311598679)
    ·
      refine ⟨165158800253694960467398019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110105866835796640311598679 165158800253694960467398019)
      ·
        refine ⟨247738200380542440701097029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165158800253694960467398019 247738200380542440701097029)
        ·
          refine ⟨46450912571351707631455693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 247738200380542440701097029 46450912571351707631455693)
          ·
            refine ⟨17419092214256890361795885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46450912571351707631455693 17419092214256890361795885)
            ·
              refine ⟨6532159580346333885673457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17419092214256890361795885 6532159580346333885673457)
              ·
                refine ⟨4899119685259750414255093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6532159580346333885673457 4899119685259750414255093)
                ·
                  refine ⟨459292470493101601336415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4899119685259750414255093 459292470493101601336415)
                  ·
                    rfl

theorem cell21_2012555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 3, 2, 5].length) (baseStart_2012555 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2012555 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2012555 prefixEnd_2012555 := by exact prefixLift 2012555
  have htrace : WordTrace (prefixWord ++ tailWord_2012555) baseStart_2012555 baseEnd_2012555 := by
    simpa [prefixWord, tailWord_2012555, baseEnd_2012555] using wordTrace_append hprefix tailTrace_2012555
  have hstable : (prefixWord ++ tailWord_2012555).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2012555).length < 2 ^ (prefixWord ++ tailWord_2012555).sum := by decide
  have hdescent : baseEnd_2012555 < baseStart_2012555 := by decide
  rcases family_descends (prefixWord ++ tailWord_2012555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2012589 : List Nat := [1, 5, 2, 2, 1, 2, 2, 1, 5]
def baseStart_2012589 : Nat := 118140960795 + 2012589 * 2 ^ 59
def prefixEnd_2012589 : Nat := 4983230072969 + 3 ^ 40 * 2012589 * 2
def baseEnd_2012589 : Nat := 459300229756325097769679

theorem tailTrace_2012589 : CollatzResearch.WordTrace tailWord_2012589 prefixEnd_2012589 459300229756325097769679 := by
  unfold tailWord_2012589
  simp only [CollatzResearch.WordTrace]
  refine ⟨73405151305741250681136821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48936767537160833787424547 73405151305741250681136821)
  ·
    refine ⟨6881732934913242251356577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 73405151305741250681136821 6881732934913242251356577)
    ·
      refine ⟨5161299701184931688517433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6881732934913242251356577 5161299701184931688517433)
      ·
        refine ⟨3870974775888698766388075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5161299701184931688517433 3870974775888698766388075)
        ·
          refine ⟨5806462163833048149582113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3870974775888698766388075 5806462163833048149582113)
          ·
            refine ⟨4354846622874786112186585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5806462163833048149582113 4354846622874786112186585)
            ·
              refine ⟨3266134967156089584139939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4354846622874786112186585 3266134967156089584139939)
              ·
                refine ⟨4899202450734134376209909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3266134967156089584139939 4899202450734134376209909)
                ·
                  refine ⟨459300229756325097769679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4899202450734134376209909 459300229756325097769679)
                  ·
                    rfl

theorem cell21_2012589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 2, 1, 5].length) (baseStart_2012589 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2012589 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2012589 prefixEnd_2012589 := by exact prefixLift 2012589
  have htrace : WordTrace (prefixWord ++ tailWord_2012589) baseStart_2012589 baseEnd_2012589 := by
    simpa [prefixWord, tailWord_2012589, baseEnd_2012589] using wordTrace_append hprefix tailTrace_2012589
  have hstable : (prefixWord ++ tailWord_2012589).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2012589).length < 2 ^ (prefixWord ++ tailWord_2012589).sum := by decide
  have hdescent : baseEnd_2012589 < baseStart_2012589 := by decide
  rcases family_descends (prefixWord ++ tailWord_2012589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2012721 : List Nat := [1, 2, 2, 3, 1, 1, 1, 2, 8]
def baseStart_2012721 : Nat := 118140960795 + 2012721 * 2 ^ 59
def prefixEnd_2012721 : Nat := 4983230072969 + 3 ^ 40 * 2012721 * 2
def baseEnd_2012721 : Nat := 459330353954722201569409

theorem tailTrace_2012721 : CollatzResearch.WordTrace tailWord_2012721 prefixEnd_2012721 459330353954722201569409 := by
  unfold tailWord_2012721
  simp only [CollatzResearch.WordTrace]
  refine ⟨73409965741263037224942017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48939977160842024816628011 73409965741263037224942017)
  ·
    refine ⟨55057474305947277918706513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73409965741263037224942017 55057474305947277918706513)
    ·
      refine ⟨41293105729460458439029885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55057474305947277918706513 41293105729460458439029885)
      ·
        refine ⟨15484914648547671914636207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41293105729460458439029885 15484914648547671914636207)
        ·
          refine ⟨23227371972821507871954311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15484914648547671914636207 23227371972821507871954311)
          ·
            refine ⟨34841057959232261807931467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23227371972821507871954311 34841057959232261807931467)
            ·
              refine ⟨52261586938848392711897201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34841057959232261807931467 52261586938848392711897201)
              ·
                refine ⟨39196190204136294533922901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52261586938848392711897201 39196190204136294533922901)
                ·
                  refine ⟨459330353954722201569409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39196190204136294533922901 459330353954722201569409)
                  ·
                    rfl

theorem cell21_2012721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 2, 8].length) (baseStart_2012721 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2012721 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2012721 prefixEnd_2012721 := by exact prefixLift 2012721
  have htrace : WordTrace (prefixWord ++ tailWord_2012721) baseStart_2012721 baseEnd_2012721 := by
    simpa [prefixWord, tailWord_2012721, baseEnd_2012721] using wordTrace_append hprefix tailTrace_2012721
  have hstable : (prefixWord ++ tailWord_2012721).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2012721).length < 2 ^ (prefixWord ++ tailWord_2012721).sum := by decide
  have hdescent : baseEnd_2012721 < baseStart_2012721 := by decide
  rcases family_descends (prefixWord ++ tailWord_2012721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2012786 : List Nat := [3, 2, 1, 2, 3, 3, 2, 5]
def baseStart_2012786 : Nat := 118140960795 + 2012786 * 2 ^ 59
def prefixEnd_2012786 : Nat := 4983230072969 + 3 ^ 40 * 2012786 * 2
def baseEnd_2012786 : Nat := 153115062613432177661981

theorem tailTrace_2012786 : CollatzResearch.WordTrace tailWord_2012786 prefixEnd_2012786 153115062613432177661981 := by
  unfold tailWord_2012786
  simp only [CollatzResearch.WordTrace]
  refine ⟨18353084121506888331514553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48941557657351702217372141 18353084121506888331514553)
  ·
    refine ⟨13764813091130166248635915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18353084121506888331514553 13764813091130166248635915)
    ·
      refine ⟨20647219636695249372953873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13764813091130166248635915 20647219636695249372953873)
      ·
        refine ⟨15485414727521437029715405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20647219636695249372953873 15485414727521437029715405)
        ·
          refine ⟨5807030522820538886143277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15485414727521437029715405 5807030522820538886143277)
          ·
            refine ⟨2177636446057702082303729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5807030522820538886143277 2177636446057702082303729)
            ·
              refine ⟨1633227334543276561727797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2177636446057702082303729 1633227334543276561727797)
              ·
                refine ⟨153115062613432177661981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1633227334543276561727797 153115062613432177661981)
                ·
                  rfl

theorem cell21_2012786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 2, 5].length) (baseStart_2012786 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2012786 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2012786 prefixEnd_2012786 := by exact prefixLift 2012786
  have htrace : WordTrace (prefixWord ++ tailWord_2012786) baseStart_2012786 baseEnd_2012786 := by
    simpa [prefixWord, tailWord_2012786, baseEnd_2012786] using wordTrace_append hprefix tailTrace_2012786
  have hstable : (prefixWord ++ tailWord_2012786).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2012786).length < 2 ^ (prefixWord ++ tailWord_2012786).sum := by decide
  have hdescent : baseEnd_2012786 < baseStart_2012786 := by decide
  rcases family_descends (prefixWord ++ tailWord_2012786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2012814 : List Nat := [4, 1, 1, 3, 1, 2, 2, 1, 6]
def baseStart_2012814 : Nat := 118140960795 + 2012814 * 2 ^ 59
def prefixEnd_2012814 : Nat := 4983230072969 + 3 ^ 40 * 2012814 * 2
def baseEnd_2012814 : Nat := 459351577821774706519219

theorem tailTrace_2012814 : CollatzResearch.WordTrace tailWord_2012814 prefixEnd_2012814 459351577821774706519219 := by
  unfold tailWord_2012814
  simp only [CollatzResearch.WordTrace]
  refine ⟨9176669716240764263509687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48942238486617409405384997 9176669716240764263509687)
  ·
    refine ⟨13765004574361146395264531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9176669716240764263509687 13765004574361146395264531)
    ·
      refine ⟨20647506861541719592896797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13765004574361146395264531 20647506861541719592896797)
      ·
        refine ⟨7742815073078144847336299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20647506861541719592896797 7742815073078144847336299)
        ·
          refine ⟨11614222609617217271004449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7742815073078144847336299 11614222609617217271004449)
          ·
            refine ⟨8710666957212912953253337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11614222609617217271004449 8710666957212912953253337)
            ·
              refine ⟨6533000217909684714940003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8710666957212912953253337 6533000217909684714940003)
              ·
                refine ⟨9799500326864527072410005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6533000217909684714940003 9799500326864527072410005)
                ·
                  refine ⟨459351577821774706519219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9799500326864527072410005 459351577821774706519219)
                  ·
                    rfl

theorem cell21_2012814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 2, 1, 6].length) (baseStart_2012814 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2012814 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2012814 prefixEnd_2012814 := by exact prefixLift 2012814
  have htrace : WordTrace (prefixWord ++ tailWord_2012814) baseStart_2012814 baseEnd_2012814 := by
    simpa [prefixWord, tailWord_2012814, baseEnd_2012814] using wordTrace_append hprefix tailTrace_2012814
  have hstable : (prefixWord ++ tailWord_2012814).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2012814).length < 2 ^ (prefixWord ++ tailWord_2012814).sum := by decide
  have hdescent : baseEnd_2012814 < baseStart_2012814 := by decide
  rcases family_descends (prefixWord ++ tailWord_2012814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2012890 : List Nat := [3, 1, 1, 2, 2, 3, 2, 3, 4]
def baseStart_2012890 : Nat := 118140960795 + 2012890 * 2 ^ 59
def prefixEnd_2012890 : Nat := 4983230072969 + 3 ^ 40 * 2012890 * 2
def baseEnd_2012890 : Nat := 459368922057215463252397

theorem tailTrace_2012890 : CollatzResearch.WordTrace tailWord_2012890 prefixEnd_2012890 459368922057215463252397 := by
  unfold tailWord_2012890
  simp only [CollatzResearch.WordTrace]
  refine ⟨18354032419412694771961031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48944086451767186058562749 18354032419412694771961031)
  ·
    refine ⟨27531048629119042157941547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18354032419412694771961031 27531048629119042157941547)
    ·
      refine ⟨41296572943678563236912321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27531048629119042157941547 41296572943678563236912321)
      ·
        refine ⟨30972429707758922427684241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41296572943678563236912321 30972429707758922427684241)
        ·
          refine ⟨23229322280819191820763181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30972429707758922427684241 23229322280819191820763181)
          ·
            refine ⟨8710995855307196932786193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23229322280819191820763181 8710995855307196932786193)
            ·
              refine ⟨6533246891480397699589645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8710995855307196932786193 6533246891480397699589645)
              ·
                refine ⟨2449967584305149137346117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6533246891480397699589645 2449967584305149137346117)
                ·
                  refine ⟨459368922057215463252397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2449967584305149137346117 459368922057215463252397)
                  ·
                    rfl

theorem cell21_2012890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 2, 3, 4].length) (baseStart_2012890 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2012890 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2012890 prefixEnd_2012890 := by exact prefixLift 2012890
  have htrace : WordTrace (prefixWord ++ tailWord_2012890) baseStart_2012890 baseEnd_2012890 := by
    simpa [prefixWord, tailWord_2012890, baseEnd_2012890] using wordTrace_append hprefix tailTrace_2012890
  have hstable : (prefixWord ++ tailWord_2012890).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2012890).length < 2 ^ (prefixWord ++ tailWord_2012890).sum := by decide
  have hdescent : baseEnd_2012890 < baseStart_2012890 := by decide
  rcases family_descends (prefixWord ++ tailWord_2012890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2012893 : List Nat := [1, 4, 3, 3, 1, 1, 1, 2, 5]
def baseStart_2012893 : Nat := 118140960795 + 2012893 * 2 ^ 59
def prefixEnd_2012893 : Nat := 4983230072969 + 3 ^ 40 * 2012893 * 2
def baseEnd_2012893 : Nat := 459369606698088124702391

theorem tailTrace_2012893 : CollatzResearch.WordTrace tailWord_2012893 prefixEnd_2012893 459369606698088124702391 := by
  unfold tailWord_2012893
  simp only [CollatzResearch.WordTrace]
  refine ⟨73416239096639910600203333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48944159397759940400135555 73416239096639910600203333)
  ·
    refine ⟨13765544830619983237538125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73416239096639910600203333 13765544830619983237538125)
    ·
      refine ⟨5162079311482493714076797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13765544830619983237538125 5162079311482493714076797)
      ·
        refine ⟨1935779741805935142778799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5162079311482493714076797 1935779741805935142778799)
        ·
          refine ⟨2903669612708902714168199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1935779741805935142778799 2903669612708902714168199)
          ·
            refine ⟨4355504419063354071252299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2903669612708902714168199 4355504419063354071252299)
            ·
              refine ⟨6533256628595031106878449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4355504419063354071252299 6533256628595031106878449)
              ·
                refine ⟨4899942471446273330158837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6533256628595031106878449 4899942471446273330158837)
                ·
                  refine ⟨459369606698088124702391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4899942471446273330158837 459369606698088124702391)
                  ·
                    rfl

theorem cell21_2012893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 1, 2, 5].length) (baseStart_2012893 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2012893 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2012893 prefixEnd_2012893 := by exact prefixLift 2012893
  have htrace : WordTrace (prefixWord ++ tailWord_2012893) baseStart_2012893 baseEnd_2012893 := by
    simpa [prefixWord, tailWord_2012893, baseEnd_2012893] using wordTrace_append hprefix tailTrace_2012893
  have hstable : (prefixWord ++ tailWord_2012893).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2012893).length < 2 ^ (prefixWord ++ tailWord_2012893).sum := by decide
  have hdescent : baseEnd_2012893 < baseStart_2012893 := by decide
  rcases family_descends (prefixWord ++ tailWord_2012893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2013132 : List Nat := [2, 2, 1, 4, 1, 3, 1, 7]
def baseStart_2013132 : Nat := 118140960795 + 2013132 * 2 ^ 59
def prefixEnd_2013132 : Nat := 4983230072969 + 3 ^ 40 * 2013132 * 2
def baseEnd_2013132 : Nat := 153141383251425606739523

theorem tailTrace_2013132 : CollatzResearch.WordTrace tailWord_2013132 prefixEnd_2013132 153141383251425606739523 := by
  unfold tailWord_2013132
  simp only [CollatzResearch.WordTrace]
  refine ⟨36712478071387027209076825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48949970761849369612102433 36712478071387027209076825)
  ·
    refine ⟨27534358553540270406807619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36712478071387027209076825 27534358553540270406807619)
    ·
      refine ⟨41301537830310405610211429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27534358553540270406807619 41301537830310405610211429)
      ·
        refine ⟨7744038343183201051914643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41301537830310405610211429 7744038343183201051914643)
        ·
          refine ⟨11616057514774801577871965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7744038343183201051914643 11616057514774801577871965)
          ·
            refine ⟨4356021568040550591701987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11616057514774801577871965 4356021568040550591701987)
            ·
              refine ⟨6534032352060825887552981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4356021568040550591701987 6534032352060825887552981)
              ·
                refine ⟨153141383251425606739523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6534032352060825887552981 153141383251425606739523)
                ·
                  rfl

theorem cell21_2013132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 1, 7].length) (baseStart_2013132 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2013132 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2013132 prefixEnd_2013132 := by exact prefixLift 2013132
  have htrace : WordTrace (prefixWord ++ tailWord_2013132) baseStart_2013132 baseEnd_2013132 := by
    simpa [prefixWord, tailWord_2013132, baseEnd_2013132] using wordTrace_append hprefix tailTrace_2013132
  have hstable : (prefixWord ++ tailWord_2013132).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2013132).length < 2 ^ (prefixWord ++ tailWord_2013132).sum := by decide
  have hdescent : baseEnd_2013132 < baseStart_2013132 := by decide
  rcases family_descends (prefixWord ++ tailWord_2013132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2013138 : List Nat := [3, 2, 2, 3, 2, 2, 1, 3, 3]
def baseStart_2013138 : Nat := 118140960795 + 2013138 * 2 ^ 59
def prefixEnd_2013138 : Nat := 4983230072969 + 3 ^ 40 * 2013138 * 2
def baseEnd_2013138 : Nat := 459425519036022143118557

theorem tailTrace_2013138 : CollatzResearch.WordTrace tailWord_2013138 prefixEnd_2013138 459425519036022143118557 := by
  unfold tailWord_2013138
  simp only [CollatzResearch.WordTrace]
  refine ⟨18356293745188079360718017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48950116653834878295248045 18356293745188079360718017)
  ·
    refine ⟨13767220308891059520538513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18356293745188079360718017 13767220308891059520538513)
    ·
      refine ⟨10325415231668294640403885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13767220308891059520538513 10325415231668294640403885)
      ·
        refine ⟨3872030711875610490151457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10325415231668294640403885 3872030711875610490151457)
        ·
          refine ⟨2904023033906707867613593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3872030711875610490151457 2904023033906707867613593)
          ·
            refine ⟨2178017275430030900710195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2904023033906707867613593 2178017275430030900710195)
            ·
              refine ⟨3267025913145046351065293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2178017275430030900710195 3267025913145046351065293)
              ·
                refine ⟨1225134717429392381649485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3267025913145046351065293 1225134717429392381649485)
                ·
                  refine ⟨459425519036022143118557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1225134717429392381649485 459425519036022143118557)
                  ·
                    rfl

theorem cell21_2013138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 1, 3, 3].length) (baseStart_2013138 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2013138 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2013138 prefixEnd_2013138 := by exact prefixLift 2013138
  have htrace : WordTrace (prefixWord ++ tailWord_2013138) baseStart_2013138 baseEnd_2013138 := by
    simpa [prefixWord, tailWord_2013138, baseEnd_2013138] using wordTrace_append hprefix tailTrace_2013138
  have hstable : (prefixWord ++ tailWord_2013138).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2013138).length < 2 ^ (prefixWord ++ tailWord_2013138).sum := by decide
  have hdescent : baseEnd_2013138 < baseStart_2013138 := by decide
  rcases family_descends (prefixWord ++ tailWord_2013138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2013149 : List Nat := [1, 4, 3, 1, 3, 2, 7]
def baseStart_2013149 : Nat := 118140960795 + 2013149 * 2 ^ 59
def prefixEnd_2013149 : Nat := 4983230072969 + 3 ^ 40 * 2013149 * 2
def baseEnd_2013149 : Nat := 51047558820654285381689

theorem tailTrace_2013149 : CollatzResearch.WordTrace tailWord_2013149 prefixEnd_2013149 51047558820654285381689 := by
  unfold tailWord_2013149
  simp only [CollatzResearch.WordTrace]
  refine ⟨73425576183712466321522501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48950384122474977547681667 73425576183712466321522501)
  ·
    refine ⟨13767295534446087435285469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73425576183712466321522501 13767295534446087435285469)
    ·
      refine ⟨5162735825417282788232051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13767295534446087435285469 5162735825417282788232051)
      ·
        refine ⟨7744103738125924182348077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5162735825417282788232051 7744103738125924182348077)
        ·
          refine ⟨2904038901797221568380529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7744103738125924182348077 2904038901797221568380529)
          ·
            refine ⟨2178029176347916176285397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2904038901797221568380529 2178029176347916176285397)
            ·
              refine ⟨51047558820654285381689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2178029176347916176285397 51047558820654285381689)
              ·
                rfl

theorem cell21_2013149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 7].length) (baseStart_2013149 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2013149 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2013149 prefixEnd_2013149 := by exact prefixLift 2013149
  have htrace : WordTrace (prefixWord ++ tailWord_2013149) baseStart_2013149 baseEnd_2013149 := by
    simpa [prefixWord, tailWord_2013149, baseEnd_2013149] using wordTrace_append hprefix tailTrace_2013149
  have hstable : (prefixWord ++ tailWord_2013149).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2013149).length < 2 ^ (prefixWord ++ tailWord_2013149).sum := by decide
  have hdescent : baseEnd_2013149 < baseStart_2013149 := by decide
  rcases family_descends (prefixWord ++ tailWord_2013149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2013163 : List Nat := [1, 1, 1, 1, 2, 3, 1, 8, 3]
def baseStart_2013163 : Nat := 118140960795 + 2013163 * 2 ^ 59
def prefixEnd_2013163 : Nat := 4983230072969 + 3 ^ 40 * 2013163 * 2
def baseEnd_2013163 : Nat := 459431224376627655201839

theorem tailTrace_2013163 : CollatzResearch.WordTrace tailWord_2013163 prefixEnd_2013163 459431224376627655201839 := by
  unfold tailWord_2013163
  simp only [CollatzResearch.WordTrace]
  refine ⟨73426086805661746712532143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48950724537107831141688095 73426086805661746712532143)
  ·
    refine ⟨110139130208492620068798215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73426086805661746712532143 110139130208492620068798215)
    ·
      refine ⟨165208695312738930103197323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110139130208492620068798215 165208695312738930103197323)
      ·
        refine ⟨247813042969108395154795985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165208695312738930103197323 247813042969108395154795985)
        ·
          refine ⟨185859782226831296366096989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 247813042969108395154795985 185859782226831296366096989)
          ·
            refine ⟨69697418335061736137286371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 185859782226831296366096989 69697418335061736137286371)
            ·
              refine ⟨104546127502592604205929557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69697418335061736137286371 104546127502592604205929557)
              ·
                refine ⟨1225149931671007080538237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 104546127502592604205929557 1225149931671007080538237)
                ·
                  refine ⟨459431224376627655201839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1225149931671007080538237 459431224376627655201839)
                  ·
                    rfl

theorem cell21_2013163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 8, 3].length) (baseStart_2013163 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2013163 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2013163 prefixEnd_2013163 := by exact prefixLift 2013163
  have htrace : WordTrace (prefixWord ++ tailWord_2013163) baseStart_2013163 baseEnd_2013163 := by
    simpa [prefixWord, tailWord_2013163, baseEnd_2013163] using wordTrace_append hprefix tailTrace_2013163
  have hstable : (prefixWord ++ tailWord_2013163).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2013163).length < 2 ^ (prefixWord ++ tailWord_2013163).sum := by decide
  have hdescent : baseEnd_2013163 < baseStart_2013163 := by decide
  rcases family_descends (prefixWord ++ tailWord_2013163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2013377 : List Nat := [1, 2, 6, 1, 3, 8]
def baseStart_2013377 : Nat := 118140960795 + 2013377 * 2 ^ 59
def prefixEnd_2013377 : Nat := 4983230072969 + 3 ^ 40 * 2013377 * 2
def baseEnd_2013377 : Nat := 17017780077489290319805

theorem tailTrace_2013377 : CollatzResearch.WordTrace tailWord_2013377 prefixEnd_2013377 17017780077489290319805 := by
  unfold tailWord_2013377
  simp only [CollatzResearch.WordTrace]
  refine ⟨73433892026886461260822385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48955928017924307507214923 73433892026886461260822385)
  ·
    refine ⟨55075419020164845945616789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73433892026886461260822385 55075419020164845945616789)
    ·
      refine ⟨2581660266570227153700787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 55075419020164845945616789 2581660266570227153700787)
      ·
        refine ⟨3872490399855340730551181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2581660266570227153700787 3872490399855340730551181)
        ·
          refine ⟨1452183899945752773956693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3872490399855340730551181 1452183899945752773956693)
          ·
            refine ⟨17017780077489290319805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1452183899945752773956693 17017780077489290319805)
            ·
              rfl

theorem cell21_2013377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 8].length) (baseStart_2013377 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2013377 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2013377 prefixEnd_2013377 := by exact prefixLift 2013377
  have htrace : WordTrace (prefixWord ++ tailWord_2013377) baseStart_2013377 baseEnd_2013377 := by
    simpa [prefixWord, tailWord_2013377, baseEnd_2013377] using wordTrace_append hprefix tailTrace_2013377
  have hstable : (prefixWord ++ tailWord_2013377).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2013377).length < 2 ^ (prefixWord ++ tailWord_2013377).sum := by decide
  have hdescent : baseEnd_2013377 < baseStart_2013377 := by decide
  rcases family_descends (prefixWord ++ tailWord_2013377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2013391 : List Nat := [1, 1, 2, 1, 1, 3, 5, 4, 3]
def baseStart_2013391 : Nat := 118140960795 + 2013391 * 2 ^ 59
def prefixEnd_2013391 : Nat := 4983230072969 + 3 ^ 40 * 2013391 * 2
def baseEnd_2013391 : Nat := 459483257082949925401373

theorem tailTrace_2013391 : CollatzResearch.WordTrace tailWord_2013391 prefixEnd_2013391 459483257082949925401373 := by
  unfold tailWord_2013391
  simp only [CollatzResearch.WordTrace]
  refine ⟨73434402648835741651832027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48956268432557161101221351 73434402648835741651832027)
  ·
    refine ⟨110151603973253612477748041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73434402648835741651832027 110151603973253612477748041)
    ·
      refine ⟨82613702979940209358311031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110151603973253612477748041 82613702979940209358311031)
      ·
        refine ⟨123920554469910314037466547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82613702979940209358311031 123920554469910314037466547)
        ·
          refine ⟨185880831704865471056199821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123920554469910314037466547 185880831704865471056199821)
          ·
            refine ⟨69705311889324551646074933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 185880831704865471056199821 69705311889324551646074933)
            ·
              refine ⟨6534872989624176716819525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 69705311889324551646074933 6534872989624176716819525)
              ·
                refine ⟨1225288685554533134403661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6534872989624176716819525 1225288685554533134403661)
                ·
                  refine ⟨459483257082949925401373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1225288685554533134403661 459483257082949925401373)
                  ·
                    rfl

theorem cell21_2013391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 5, 4, 3].length) (baseStart_2013391 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2013391 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2013391 prefixEnd_2013391 := by exact prefixLift 2013391
  have htrace : WordTrace (prefixWord ++ tailWord_2013391) baseStart_2013391 baseEnd_2013391 := by
    simpa [prefixWord, tailWord_2013391, baseEnd_2013391] using wordTrace_append hprefix tailTrace_2013391
  have hstable : (prefixWord ++ tailWord_2013391).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2013391).length < 2 ^ (prefixWord ++ tailWord_2013391).sum := by decide
  have hdescent : baseEnd_2013391 < baseStart_2013391 := by decide
  rcases family_descends (prefixWord ++ tailWord_2013391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2013450 : List Nat := [3, 1, 2, 2, 1, 1, 3, 3, 5]
def baseStart_2013450 : Nat := 118140960795 + 2013450 * 2 ^ 59
def prefixEnd_2013450 : Nat := 4983230072969 + 3 ^ 40 * 2013450 * 2
def baseEnd_2013450 : Nat := 459496721686778933917919

theorem tailTrace_2013450 : CollatzResearch.WordTrace tailWord_2013450 prefixEnd_2013450 459496721686778933917919 := by
  unfold tailWord_2013450
  simp only [CollatzResearch.WordTrace]
  refine ⟨18359138638905498682057451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48957703037081329818819869 18359138638905498682057451)
  ·
    refine ⟨27538707958358248023086177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18359138638905498682057451 27538707958358248023086177)
    ·
      refine ⟨20654030968768686017314633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27538707958358248023086177 20654030968768686017314633)
      ·
        refine ⟨15490523226576514512985975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20654030968768686017314633 15490523226576514512985975)
        ·
          refine ⟨23235784839864771769478963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15490523226576514512985975 23235784839864771769478963)
          ·
            refine ⟨34853677259797157654218445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23235784839864771769478963 34853677259797157654218445)
            ·
              refine ⟨13070128972423934120331917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34853677259797157654218445 13070128972423934120331917)
              ·
                refine ⟨4901298364658975295124469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13070128972423934120331917 4901298364658975295124469)
                ·
                  refine ⟨459496721686778933917919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4901298364658975295124469 459496721686778933917919)
                  ·
                    rfl

theorem cell21_2013450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 3, 5].length) (baseStart_2013450 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2013450 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2013450 prefixEnd_2013450 := by exact prefixLift 2013450
  have htrace : WordTrace (prefixWord ++ tailWord_2013450) baseStart_2013450 baseEnd_2013450 := by
    simpa [prefixWord, tailWord_2013450, baseEnd_2013450] using wordTrace_append hprefix tailTrace_2013450
  have hstable : (prefixWord ++ tailWord_2013450).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2013450).length < 2 ^ (prefixWord ++ tailWord_2013450).sum := by decide
  have hdescent : baseEnd_2013450 < baseStart_2013450 := by decide
  rcases family_descends (prefixWord ++ tailWord_2013450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2013470 : List Nat := [4, 3, 2, 1, 1, 1, 4, 5]
def baseStart_2013470 : Nat := 118140960795 + 2013470 * 2 ^ 59
def prefixEnd_2013470 : Nat := 4983230072969 + 3 ^ 40 * 2013470 * 2
def baseEnd_2013470 : Nat := 153167095319754447861515

theorem tailTrace_2013470 : CollatzResearch.WordTrace tailWord_2013470 prefixEnd_2013470 153167095319754447861515 := by
  unfold tailWord_2013470
  simp only [CollatzResearch.WordTrace]
  refine ⟨9179660501943692267994733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48958189343699692095971909 9179660501943692267994733)
  ·
    refine ⟨3442372688228884600498025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9179660501943692267994733 3442372688228884600498025)
    ·
      refine ⟨2581779516171663450373519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3442372688228884600498025 2581779516171663450373519)
      ·
        refine ⟨3872669274257495175560279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2581779516171663450373519 3872669274257495175560279)
        ·
          refine ⟨5809003911386242763340419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3872669274257495175560279 5809003911386242763340419)
          ·
            refine ⟨8713505867079364145010629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5809003911386242763340419 8713505867079364145010629)
            ·
              refine ⟨1633782350077380777189493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8713505867079364145010629 1633782350077380777189493)
              ·
                refine ⟨153167095319754447861515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1633782350077380777189493 153167095319754447861515)
                ·
                  rfl

theorem cell21_2013470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 4, 5].length) (baseStart_2013470 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2013470 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2013470 prefixEnd_2013470 := by exact prefixLift 2013470
  have htrace : WordTrace (prefixWord ++ tailWord_2013470) baseStart_2013470 baseEnd_2013470 := by
    simpa [prefixWord, tailWord_2013470, baseEnd_2013470] using wordTrace_append hprefix tailTrace_2013470
  have hstable : (prefixWord ++ tailWord_2013470).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2013470).length < 2 ^ (prefixWord ++ tailWord_2013470).sum := by decide
  have hdescent : baseEnd_2013470 < baseStart_2013470 := by decide
  rcases family_descends (prefixWord ++ tailWord_2013470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2013602 : List Nat := [3, 3, 1, 2, 1, 1, 1, 2, 7]
def baseStart_2013602 : Nat := 118140960795 + 2013602 * 2 ^ 59
def prefixEnd_2013602 : Nat := 4983230072969 + 3 ^ 40 * 2013602 * 2
def baseEnd_2013602 : Nat := 459531410157660447384275

theorem tailTrace_2013602 : CollatzResearch.WordTrace tailWord_2013602 prefixEnd_2013602 459531410157660447384275 := by
  unfold tailWord_2013602
  simp only [CollatzResearch.WordTrace]
  refine ⟨18360524612767831171940765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48961398967380883125175373 18360524612767831171940765)
  ·
    refine ⟨6885196729787936689477787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18360524612767831171940765 6885196729787936689477787)
    ·
      refine ⟨10327795094681905034216681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6885196729787936689477787 10327795094681905034216681)
      ·
        refine ⟨7745846321011428775662511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10327795094681905034216681 7745846321011428775662511)
        ·
          refine ⟨11618769481517143163493767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7745846321011428775662511 11618769481517143163493767)
          ·
            refine ⟨17428154222275714745240651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11618769481517143163493767 17428154222275714745240651)
            ·
              refine ⟨26142231333413572117860977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17428154222275714745240651 26142231333413572117860977)
              ·
                refine ⟨19606673500060179088395733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26142231333413572117860977 19606673500060179088395733)
                ·
                  refine ⟨459531410157660447384275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19606673500060179088395733 459531410157660447384275)
                  ·
                    rfl

theorem cell21_2013602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 2, 7].length) (baseStart_2013602 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2013602 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2013602 prefixEnd_2013602 := by exact prefixLift 2013602
  have htrace : WordTrace (prefixWord ++ tailWord_2013602) baseStart_2013602 baseEnd_2013602 := by
    simpa [prefixWord, tailWord_2013602, baseEnd_2013602] using wordTrace_append hprefix tailTrace_2013602
  have hstable : (prefixWord ++ tailWord_2013602).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2013602).length < 2 ^ (prefixWord ++ tailWord_2013602).sum := by decide
  have hdescent : baseEnd_2013602 < baseStart_2013602 := by decide
  rcases family_descends (prefixWord ++ tailWord_2013602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2013754 : List Nat := [3, 1, 1, 1, 3, 4, 1, 2, 5]
def baseStart_2013754 : Nat := 118140960795 + 2013754 * 2 ^ 59
def prefixEnd_2013754 : Nat := 4983230072969 + 3 ^ 40 * 2013754 * 2
def baseEnd_2013754 : Nat := 459566098628541960850631

theorem tailTrace_2013754 : CollatzResearch.WordTrace tailWord_2013754 prefixEnd_2013754 459566098628541960850631 := by
  unfold tailWord_2013754
  simp only [CollatzResearch.WordTrace]
  refine ⟨18361910586630163661824079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48965094897680436431530877 18361910586630163661824079)
  ·
    refine ⟨27542865879945245492736119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18361910586630163661824079 27542865879945245492736119)
    ·
      refine ⟨41314298819917868239104179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27542865879945245492736119 41314298819917868239104179)
      ·
        refine ⟨61971448229876802358656269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41314298819917868239104179 61971448229876802358656269)
        ·
          refine ⟨23239293086203800884496101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61971448229876802358656269 23239293086203800884496101)
          ·
            refine ⟨4357367453663212665843019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23239293086203800884496101 4357367453663212665843019)
            ·
              refine ⟨6536051180494818998764529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4357367453663212665843019 6536051180494818998764529)
              ·
                refine ⟨4902038385371114249073397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6536051180494818998764529 4902038385371114249073397)
                ·
                  refine ⟨459566098628541960850631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4902038385371114249073397 459566098628541960850631)
                  ·
                    rfl

theorem cell21_2013754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 1, 2, 5].length) (baseStart_2013754 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2013754 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2013754 prefixEnd_2013754 := by exact prefixLift 2013754
  have htrace : WordTrace (prefixWord ++ tailWord_2013754) baseStart_2013754 baseEnd_2013754 := by
    simpa [prefixWord, tailWord_2013754, baseEnd_2013754] using wordTrace_append hprefix tailTrace_2013754
  have hstable : (prefixWord ++ tailWord_2013754).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2013754).length < 2 ^ (prefixWord ++ tailWord_2013754).sum := by decide
  have hdescent : baseEnd_2013754 < baseStart_2013754 := by decide
  rcases family_descends (prefixWord ++ tailWord_2013754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2013802 : List Nat := [3, 1, 3, 2, 1, 1, 5, 1, 4]
def baseStart_2013802 : Nat := 118140960795 + 2013802 * 2 ^ 59
def prefixEnd_2013802 : Nat := 4983230072969 + 3 ^ 40 * 2013802 * 2
def baseEnd_2013802 : Nat := 459577052882504544050533

theorem tailTrace_2013802 : CollatzResearch.WordTrace tailWord_2013802 prefixEnd_2013802 459577052882504544050533 := by
  unfold tailWord_2013802
  simp only [CollatzResearch.WordTrace]
  refine ⟨18362348262586689711260915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48966262033564505896695773 18362348262586689711260915)
  ·
    refine ⟨27543522393880034566891373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18362348262586689711260915 27543522393880034566891373)
    ·
      refine ⟨10328820897705012962584265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27543522393880034566891373 10328820897705012962584265)
      ·
        refine ⟨7746615673278759721938199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10328820897705012962584265 7746615673278759721938199)
        ·
          refine ⟨11619923509918139582907299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7746615673278759721938199 11619923509918139582907299)
          ·
            refine ⟨17429885264877209374360949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11619923509918139582907299 17429885264877209374360949)
            ·
              refine ⟨1634051743582238378846339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17429885264877209374360949 1634051743582238378846339)
              ·
                refine ⟨2451077615373357568269509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1634051743582238378846339 2451077615373357568269509)
                ·
                  refine ⟨459577052882504544050533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2451077615373357568269509 459577052882504544050533)
                  ·
                    rfl

theorem cell21_2013802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 5, 1, 4].length) (baseStart_2013802 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2013802 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2013802 prefixEnd_2013802 := by exact prefixLift 2013802
  have htrace : WordTrace (prefixWord ++ tailWord_2013802) baseStart_2013802 baseEnd_2013802 := by
    simpa [prefixWord, tailWord_2013802, baseEnd_2013802] using wordTrace_append hprefix tailTrace_2013802
  have hstable : (prefixWord ++ tailWord_2013802).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2013802).length < 2 ^ (prefixWord ++ tailWord_2013802).sum := by decide
  have hdescent : baseEnd_2013802 < baseStart_2013802 := by decide
  rcases family_descends (prefixWord ++ tailWord_2013802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2013909 : List Nat := [1, 3, 2, 5, 1, 2, 1, 6]
def baseStart_2013909 : Nat := 118140960795 + 2013909 * 2 ^ 59
def prefixEnd_2013909 : Nat := 4983230072969 + 3 ^ 40 * 2013909 * 2
def baseEnd_2013909 : Nat := 153200490580098711922327

theorem tailTrace_2013909 : CollatzResearch.WordTrace tailWord_2013909 prefixEnd_2013909 153200490580098711922327 := by
  unfold tailWord_2013909
  simp only [CollatzResearch.WordTrace]
  refine ⟨73453295660959116119188781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48968863773972744079459187 73453295660959116119188781)
  ·
    refine ⟨27544985872859668544695793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73453295660959116119188781 27544985872859668544695793)
    ·
      refine ⟨20658739404644751408521845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27544985872859668544695793 20658739404644751408521845)
      ·
        refine ⟨1936756819185445444548923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20658739404644751408521845 1936756819185445444548923)
        ·
          refine ⟨2905135228778168166823385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1936756819185445444548923 2905135228778168166823385)
          ·
            refine ⟨2178851421583626125117539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2905135228778168166823385 2178851421583626125117539)
            ·
              refine ⟨3268277132375439187676309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2178851421583626125117539 3268277132375439187676309)
              ·
                refine ⟨153200490580098711922327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3268277132375439187676309 153200490580098711922327)
                ·
                  rfl

theorem cell21_2013909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 1, 6].length) (baseStart_2013909 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2013909 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2013909 prefixEnd_2013909 := by exact prefixLift 2013909
  have htrace : WordTrace (prefixWord ++ tailWord_2013909) baseStart_2013909 baseEnd_2013909 := by
    simpa [prefixWord, tailWord_2013909, baseEnd_2013909] using wordTrace_append hprefix tailTrace_2013909
  have hstable : (prefixWord ++ tailWord_2013909).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2013909).length < 2 ^ (prefixWord ++ tailWord_2013909).sum := by decide
  have hdescent : baseEnd_2013909 < baseStart_2013909 := by decide
  rcases family_descends (prefixWord ++ tailWord_2013909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2013954 : List Nat := [3, 4, 1, 1, 1, 2, 3, 2, 4]
def baseStart_2013954 : Nat := 118140960795 + 2013954 * 2 ^ 59
def prefixEnd_2013954 : Nat := 4983230072969 + 3 ^ 40 * 2013954 * 2
def baseEnd_2013954 : Nat := 459611741353386057516889

theorem tailTrace_2013954 : CollatzResearch.WordTrace tailWord_2013954 prefixEnd_2013954 459611741353386057516889 := by
  unfold tailWord_2013954
  simp only [CollatzResearch.WordTrace]
  refine ⟨18363734236449022201144229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48969957963864059203051277 18363734236449022201144229)
  ·
    refine ⟨3443200169334191662714543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18363734236449022201144229 3443200169334191662714543)
    ·
      refine ⟨5164800254001287494071815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3443200169334191662714543 5164800254001287494071815)
      ·
        refine ⟨7747200381001931241107723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5164800254001287494071815 7747200381001931241107723)
        ·
          refine ⟨11620800571502896861661585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7747200381001931241107723 11620800571502896861661585)
          ·
            refine ⟨8715600428627172646246189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11620800571502896861661585 8715600428627172646246189)
            ·
              refine ⟨3268350160735189742342321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8715600428627172646246189 3268350160735189742342321)
              ·
                refine ⟨2451262620551392306756741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3268350160735189742342321 2451262620551392306756741)
                ·
                  refine ⟨459611741353386057516889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2451262620551392306756741 459611741353386057516889)
                  ·
                    rfl

theorem cell21_2013954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 3, 2, 4].length) (baseStart_2013954 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2013954 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2013954 prefixEnd_2013954 := by exact prefixLift 2013954
  have htrace : WordTrace (prefixWord ++ tailWord_2013954) baseStart_2013954 baseEnd_2013954 := by
    simpa [prefixWord, tailWord_2013954, baseEnd_2013954] using wordTrace_append hprefix tailTrace_2013954
  have hstable : (prefixWord ++ tailWord_2013954).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2013954).length < 2 ^ (prefixWord ++ tailWord_2013954).sum := by decide
  have hdescent : baseEnd_2013954 < baseStart_2013954 := by decide
  rcases family_descends (prefixWord ++ tailWord_2013954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2013979 : List Nat := [1, 1, 1, 1, 1, 1, 4, 1, 10]
def baseStart_2013979 : Nat := 118140960795 + 2013979 * 2 ^ 59
def prefixEnd_2013979 : Nat := 4983230072969 + 3 ^ 40 * 2013979 * 2
def baseEnd_2013979 : Nat := 459617446693991569600171

theorem tailTrace_2013979 : CollatzResearch.WordTrace tailWord_2013979 prefixEnd_2013979 459617446693991569600171 := by
  unfold tailWord_2013979
  simp only [CollatzResearch.WordTrace]
  refine ⟨73455848770705518074236991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48970565847137012049491327 73455848770705518074236991)
  ·
    refine ⟨110183773156058277111355487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73455848770705518074236991 110183773156058277111355487)
    ·
      refine ⟨165275659734087415667033231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110183773156058277111355487 165275659734087415667033231)
      ·
        refine ⟨247913489601131123500549847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165275659734087415667033231 247913489601131123500549847)
        ·
          refine ⟨371870234401696685250824771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247913489601131123500549847 371870234401696685250824771)
          ·
            refine ⟨557805351602545027876237157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 371870234401696685250824771 557805351602545027876237157)
            ·
              refine ⟨104588503425477192726794467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 557805351602545027876237157 104588503425477192726794467)
              ·
                refine ⟨156882755138215789090191701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104588503425477192726794467 156882755138215789090191701)
                ·
                  refine ⟨459617446693991569600171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 156882755138215789090191701 459617446693991569600171)
                  ·
                    rfl

theorem cell21_2013979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 10].length) (baseStart_2013979 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2013979 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2013979 prefixEnd_2013979 := by exact prefixLift 2013979
  have htrace : WordTrace (prefixWord ++ tailWord_2013979) baseStart_2013979 baseEnd_2013979 := by
    simpa [prefixWord, tailWord_2013979, baseEnd_2013979] using wordTrace_append hprefix tailTrace_2013979
  have hstable : (prefixWord ++ tailWord_2013979).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2013979).length < 2 ^ (prefixWord ++ tailWord_2013979).sum := by decide
  have hdescent : baseEnd_2013979 < baseStart_2013979 := by decide
  rcases family_descends (prefixWord ++ tailWord_2013979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2014075 : List Nat := [1, 1, 1, 1, 1, 5, 6, 2, 3]
def baseStart_2014075 : Nat := 118140960795 + 2014075 * 2 ^ 59
def prefixEnd_2014075 : Nat := 4983230072969 + 3 ^ 40 * 2014075 * 2
def baseEnd_2014075 : Nat := 459639355201916735999975

theorem tailTrace_2014075 : CollatzResearch.WordTrace tailWord_2014075 prefixEnd_2014075 459639355201916735999975 := by
  unfold tailWord_2014075
  simp only [CollatzResearch.WordTrace]
  refine ⟨73459350178357726469731679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48972900118905150979821119 73459350178357726469731679)
  ·
    refine ⟨110189025267536589704597519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73459350178357726469731679 110189025267536589704597519)
    ·
      refine ⟨165283537901304884556896279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110189025267536589704597519 165283537901304884556896279)
      ·
        refine ⟨247925306851957326835344419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165283537901304884556896279 247925306851957326835344419)
        ·
          refine ⟨371887960277935990253016629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247925306851957326835344419 371887960277935990253016629)
          ·
            refine ⟨34864496276056499086220309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 371887960277935990253016629 34864496276056499086220309)
            ·
              refine ⟨1634273262940148394666577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 34864496276056499086220309 1634273262940148394666577)
              ·
                refine ⟨1225704947205111295999933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1634273262940148394666577 1225704947205111295999933)
                ·
                  refine ⟨459639355201916735999975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1225704947205111295999933 459639355201916735999975)
                  ·
                    rfl

theorem cell21_2014075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 6, 2, 3].length) (baseStart_2014075 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2014075 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2014075 prefixEnd_2014075 := by exact prefixLift 2014075
  have htrace : WordTrace (prefixWord ++ tailWord_2014075) baseStart_2014075 baseEnd_2014075 := by
    simpa [prefixWord, tailWord_2014075, baseEnd_2014075] using wordTrace_append hprefix tailTrace_2014075
  have hstable : (prefixWord ++ tailWord_2014075).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2014075).length < 2 ^ (prefixWord ++ tailWord_2014075).sum := by decide
  have hdescent : baseEnd_2014075 < baseStart_2014075 := by decide
  rcases family_descends (prefixWord ++ tailWord_2014075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2014078 : List Nat := [4, 2, 3, 1, 3, 1, 1, 6]
def baseStart_2014078 : Nat := 118140960795 + 2014078 * 2 ^ 59
def prefixEnd_2014078 : Nat := 4983230072969 + 3 ^ 40 * 2014078 * 2
def baseEnd_2014078 : Nat := 153213346614263132483323

theorem tailTrace_2014078 : CollatzResearch.WordTrace tailWord_2014078 prefixEnd_2014078 153213346614263132483323 := by
  unfold tailWord_2014078
  simp only [CollatzResearch.WordTrace]
  refine ⟨9182432449668357247761361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48972973064897905321393925 9182432449668357247761361)
  ·
    refine ⟨6886824337251267935821021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9182432449668357247761361 6886824337251267935821021)
    ·
      refine ⟨2582559126469225475932883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6886824337251267935821021 2582559126469225475932883)
      ·
        refine ⟨3873838689703838213899325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2582559126469225475932883 3873838689703838213899325)
        ·
          refine ⟨1452689508638939330212247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3873838689703838213899325 1452689508638939330212247)
          ·
            refine ⟨2179034262958408995318371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1452689508638939330212247 2179034262958408995318371)
            ·
              refine ⟨3268551394437613492977557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2179034262958408995318371 3268551394437613492977557)
              ·
                refine ⟨153213346614263132483323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3268551394437613492977557 153213346614263132483323)
                ·
                  rfl

theorem cell21_2014078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 1, 6].length) (baseStart_2014078 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2014078 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2014078 prefixEnd_2014078 := by exact prefixLift 2014078
  have htrace : WordTrace (prefixWord ++ tailWord_2014078) baseStart_2014078 baseEnd_2014078 := by
    simpa [prefixWord, tailWord_2014078, baseEnd_2014078] using wordTrace_append hprefix tailTrace_2014078
  have hstable : (prefixWord ++ tailWord_2014078).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2014078).length < 2 ^ (prefixWord ++ tailWord_2014078).sum := by decide
  have hdescent : baseEnd_2014078 < baseStart_2014078 := by decide
  rcases family_descends (prefixWord ++ tailWord_2014078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2014103 : List Nat := [1, 1, 3, 3, 1, 2, 5, 5]
def baseStart_2014103 : Nat := 118140960795 + 2014103 * 2 ^ 59
def prefixEnd_2014103 : Nat := 4983230072969 + 3 ^ 40 * 2014103 * 2
def baseEnd_2014103 : Nat := 153215248394464969844417

theorem tailTrace_2014103 : CollatzResearch.WordTrace tailWord_2014103 prefixEnd_2014103 153215248394464969844417 := by
  unfold tailWord_2014103
  simp only [CollatzResearch.WordTrace]
  refine ⟨73460371422256287251750963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48973580948170858167833975 73460371422256287251750963)
  ·
    refine ⟨110190557133384430877626445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73460371422256287251750963 110190557133384430877626445)
    ·
      refine ⟨41321458925019161579109917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110190557133384430877626445 41321458925019161579109917)
      ·
        refine ⟨15495547096882185592166219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41321458925019161579109917 15495547096882185592166219)
        ·
          refine ⟨23243320645323278388249329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15495547096882185592166219 23243320645323278388249329)
          ·
            refine ⟨17432490483992458791186997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23243320645323278388249329 17432490483992458791186997)
            ·
              refine ⟨1634295982874293011673781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17432490483992458791186997 1634295982874293011673781)
              ·
                refine ⟨153215248394464969844417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1634295982874293011673781 153215248394464969844417)
                ·
                  rfl

theorem cell21_2014103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 5, 5].length) (baseStart_2014103 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2014103 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2014103 prefixEnd_2014103 := by exact prefixLift 2014103
  have htrace : WordTrace (prefixWord ++ tailWord_2014103) baseStart_2014103 baseEnd_2014103 := by
    simpa [prefixWord, tailWord_2014103, baseEnd_2014103] using wordTrace_append hprefix tailTrace_2014103
  have hstable : (prefixWord ++ tailWord_2014103).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2014103).length < 2 ^ (prefixWord ++ tailWord_2014103).sum := by decide
  have hdescent : baseEnd_2014103 < baseStart_2014103 := by decide
  rcases family_descends (prefixWord ++ tailWord_2014103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2014238 : List Nat := [4, 3, 14]
def baseStart_2014238 : Nat := 118140960795 + 2014238 * 2 ^ 59
def prefixEnd_2014238 : Nat := 4983230072969 + 3 ^ 40 * 2014238 * 2
def baseEnd_2014238 : Nat := 630557687273888442775

theorem tailTrace_2014238 : CollatzResearch.WordTrace tailWord_2014238 prefixEnd_2014238 630557687273888442775 := by
  unfold tailWord_2014238
  simp only [CollatzResearch.WordTrace]
  refine ⟨9183161909595900663489421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48976863517844803538610245 9183161909595900663489421)
  ·
    refine ⟨3443685716098462748808533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9183161909595900663489421 3443685716098462748808533)
    ·
      refine ⟨630557687273888442775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 14 3443685716098462748808533 630557687273888442775)
      ·
        rfl

theorem cell21_2014238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 14].length) (baseStart_2014238 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2014238 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2014238 prefixEnd_2014238 := by exact prefixLift 2014238
  have htrace : WordTrace (prefixWord ++ tailWord_2014238) baseStart_2014238 baseEnd_2014238 := by
    simpa [prefixWord, tailWord_2014238, baseEnd_2014238] using wordTrace_append hprefix tailTrace_2014238
  have hstable : (prefixWord ++ tailWord_2014238).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2014238).length < 2 ^ (prefixWord ++ tailWord_2014238).sum := by decide
  have hdescent : baseEnd_2014238 < baseStart_2014238 := by decide
  rcases family_descends (prefixWord ++ tailWord_2014238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2014241 : List Nat := [1, 2, 3, 2, 3, 2, 2, 2, 4]
def baseStart_2014241 : Nat := 118140960795 + 2014241 * 2 ^ 59
def prefixEnd_2014241 : Nat := 4983230072969 + 3 ^ 40 * 2014241 * 2
def baseEnd_2014241 : Nat := 459677238663537336232969

theorem tailTrace_2014241 : CollatzResearch.WordTrace tailWord_2014241 prefixEnd_2014241 459677238663537336232969 := by
  unfold tailWord_2014241
  simp only [CollatzResearch.WordTrace]
  refine ⟨73465404695756336820274577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48976936463837557880183051 73465404695756336820274577)
  ·
    refine ⟨55099053521817252615205933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73465404695756336820274577 55099053521817252615205933)
    ·
      refine ⟨20662145070681469730702225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55099053521817252615205933 20662145070681469730702225)
      ·
        refine ⟨15496608803011102298026669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20662145070681469730702225 15496608803011102298026669)
        ·
          refine ⟨5811228301129163361760001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15496608803011102298026669 5811228301129163361760001)
          ·
            refine ⟨4358421225846872521320001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5811228301129163361760001 4358421225846872521320001)
            ·
              refine ⟨3268815919385154390990001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4358421225846872521320001 3268815919385154390990001)
              ·
                refine ⟨2451611939538865793242501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3268815919385154390990001 2451611939538865793242501)
                ·
                  refine ⟨459677238663537336232969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2451611939538865793242501 459677238663537336232969)
                  ·
                    rfl

theorem cell21_2014241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 2, 2, 4].length) (baseStart_2014241 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2014241 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2014241 prefixEnd_2014241 := by exact prefixLift 2014241
  have htrace : WordTrace (prefixWord ++ tailWord_2014241) baseStart_2014241 baseEnd_2014241 := by
    simpa [prefixWord, tailWord_2014241, baseEnd_2014241] using wordTrace_append hprefix tailTrace_2014241
  have hstable : (prefixWord ++ tailWord_2014241).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2014241).length < 2 ^ (prefixWord ++ tailWord_2014241).sum := by decide
  have hdescent : baseEnd_2014241 < baseStart_2014241 := by decide
  rcases family_descends (prefixWord ++ tailWord_2014241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2014244 : List Nat := [2, 3, 1, 4, 1, 1, 4, 2, 3]
def baseStart_2014244 : Nat := 118140960795 + 2014244 * 2 ^ 59
def prefixEnd_2014244 : Nat := 4983230072969 + 3 ^ 40 * 2014244 * 2
def baseEnd_2014244 : Nat := 459677923304409997682963

theorem tailTrace_2014244 : CollatzResearch.WordTrace tailWord_2014244 prefixEnd_2014244 459677923304409997682963 := by
  unfold tailWord_2014244
  simp only [CollatzResearch.WordTrace]
  refine ⟨36732757057372734166316893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48977009409830312221755857 36732757057372734166316893)
  ·
    refine ⟨13774783896514775312368835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36732757057372734166316893 13774783896514775312368835)
    ·
      refine ⟨20662175844772162968553253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13774783896514775312368835 20662175844772162968553253)
      ·
        refine ⟨3874157970894780556603735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20662175844772162968553253 3874157970894780556603735)
        ·
          refine ⟨5811236956342170834905603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3874157970894780556603735 5811236956342170834905603)
          ·
            refine ⟨8716855434513256252358405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5811236956342170834905603 8716855434513256252358405)
            ·
              refine ⟨1634410393971235547317201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8716855434513256252358405 1634410393971235547317201)
              ·
                refine ⟨1225807795478426660487901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1634410393971235547317201 1225807795478426660487901)
                ·
                  refine ⟨459677923304409997682963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1225807795478426660487901 459677923304409997682963)
                  ·
                    rfl

theorem cell21_2014244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 4, 2, 3].length) (baseStart_2014244 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2014244 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2014244 prefixEnd_2014244 := by exact prefixLift 2014244
  have htrace : WordTrace (prefixWord ++ tailWord_2014244) baseStart_2014244 baseEnd_2014244 := by
    simpa [prefixWord, tailWord_2014244, baseEnd_2014244] using wordTrace_append hprefix tailTrace_2014244
  have hstable : (prefixWord ++ tailWord_2014244).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2014244).length < 2 ^ (prefixWord ++ tailWord_2014244).sum := by decide
  have hdescent : baseEnd_2014244 < baseStart_2014244 := by decide
  rcases family_descends (prefixWord ++ tailWord_2014244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2014269 : List Nat := [1, 4, 1, 3, 1, 2, 1, 1, 7]
def baseStart_2014269 : Nat := 118140960795 + 2014269 * 2 ^ 59
def prefixEnd_2014269 : Nat := 4983230072969 + 3 ^ 40 * 2014269 * 2
def baseEnd_2014269 : Nat := 459683628645015509766245

theorem tailTrace_2014269 : CollatzResearch.WordTrace tailWord_2014269 prefixEnd_2014269 459683628645015509766245 := by
  unfold tailWord_2014269
  simp only [CollatzResearch.WordTrace]
  refine ⟨73466425939654897602293861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48977617293103265068195907 73466425939654897602293861)
  ·
    refine ⟨13774954863685293300430099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73466425939654897602293861 13774954863685293300430099)
    ·
      refine ⟨20662432295527939950645149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13774954863685293300430099 20662432295527939950645149)
      ·
        refine ⟨7748412110822977481491931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20662432295527939950645149 7748412110822977481491931)
        ·
          refine ⟨11622618166234466222237897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7748412110822977481491931 11622618166234466222237897)
          ·
            refine ⟨8716963624675849666678423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11622618166234466222237897 8716963624675849666678423)
            ·
              refine ⟨13075445437013774500017635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8716963624675849666678423 13075445437013774500017635)
              ·
                refine ⟨19613168155520661750026453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13075445437013774500017635 19613168155520661750026453)
                ·
                  refine ⟨459683628645015509766245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19613168155520661750026453 459683628645015509766245)
                  ·
                    rfl

theorem cell21_2014269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 1, 7].length) (baseStart_2014269 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2014269 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2014269 prefixEnd_2014269 := by exact prefixLift 2014269
  have htrace : WordTrace (prefixWord ++ tailWord_2014269) baseStart_2014269 baseEnd_2014269 := by
    simpa [prefixWord, tailWord_2014269, baseEnd_2014269] using wordTrace_append hprefix tailTrace_2014269
  have hstable : (prefixWord ++ tailWord_2014269).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2014269).length < 2 ^ (prefixWord ++ tailWord_2014269).sum := by decide
  have hdescent : baseEnd_2014269 < baseStart_2014269 := by decide
  rcases family_descends (prefixWord ++ tailWord_2014269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2014300 : List Nat := [2, 2, 4, 1, 1, 1, 3, 1, 6]
def baseStart_2014300 : Nat := 118140960795 + 2014300 * 2 ^ 59
def prefixEnd_2014300 : Nat := 4983230072969 + 3 ^ 40 * 2014300 * 2
def baseEnd_2014300 : Nat := 459690703267366344749515

theorem tailTrace_2014300 : CollatzResearch.WordTrace tailWord_2014300 prefixEnd_2014300 459690703267366344749515 := by
  unfold tailWord_2014300
  simp only [CollatzResearch.WordTrace]
  refine ⟨36733778301271294948336177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48978371068361726597781569 36733778301271294948336177)
  ·
    refine ⟨27550333725953471211252133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36733778301271294948336177 27550333725953471211252133)
    ·
      refine ⟨5165687573616275852109775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27550333725953471211252133 5165687573616275852109775)
      ·
        refine ⟨7748531360424413778164663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5165687573616275852109775 7748531360424413778164663)
        ·
          refine ⟨11622797040636620667246995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7748531360424413778164663 11622797040636620667246995)
          ·
            refine ⟨17434195560954931000870493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11622797040636620667246995 17434195560954931000870493)
            ·
              refine ⟨6537823335358099125326435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17434195560954931000870493 6537823335358099125326435)
              ·
                refine ⟨9806735003037148687989653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6537823335358099125326435 9806735003037148687989653)
                ·
                  refine ⟨459690703267366344749515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9806735003037148687989653 459690703267366344749515)
                  ·
                    rfl

theorem cell21_2014300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 3, 1, 6].length) (baseStart_2014300 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2014300 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2014300 prefixEnd_2014300 := by exact prefixLift 2014300
  have htrace : WordTrace (prefixWord ++ tailWord_2014300) baseStart_2014300 baseEnd_2014300 := by
    simpa [prefixWord, tailWord_2014300, baseEnd_2014300] using wordTrace_append hprefix tailTrace_2014300
  have hstable : (prefixWord ++ tailWord_2014300).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2014300).length < 2 ^ (prefixWord ++ tailWord_2014300).sum := by decide
  have hdescent : baseEnd_2014300 < baseStart_2014300 := by decide
  rcases family_descends (prefixWord ++ tailWord_2014300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2014362 : List Nat := [3, 1, 1, 5, 1, 1, 3, 1, 5]
def baseStart_2014362 : Nat := 118140960795 + 2014362 * 2 ^ 59
def prefixEnd_2014362 : Nat := 4983230072969 + 3 ^ 40 * 2014362 * 2
def baseEnd_2014362 : Nat := 459704852512068014716055

theorem tailTrace_2014362 : CollatzResearch.WordTrace tailWord_2014362 prefixEnd_2014362 459704852512068014716055 := by
  unfold tailWord_2014362
  simp only [CollatzResearch.WordTrace]
  refine ⟨18367454482079493621357335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48979878618878649656952893 18367454482079493621357335)
  ·
    refine ⟨27551181723119240432036003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18367454482079493621357335 27551181723119240432036003)
    ·
      refine ⟨41326772584678860648054005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27551181723119240432036003 41326772584678860648054005)
      ·
        refine ⟨3874384929813643185755063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 41326772584678860648054005 3874384929813643185755063)
        ·
          refine ⟨5811577394720464778632595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3874384929813643185755063 5811577394720464778632595)
          ·
            refine ⟨8717366092080697167948893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5811577394720464778632595 8717366092080697167948893)
            ·
              refine ⟨3269012284530261437980835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8717366092080697167948893 3269012284530261437980835)
              ·
                refine ⟨4903518426795392156971253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3269012284530261437980835 4903518426795392156971253)
                ·
                  refine ⟨459704852512068014716055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4903518426795392156971253 459704852512068014716055)
                  ·
                    rfl

theorem cell21_2014362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 3, 1, 5].length) (baseStart_2014362 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2014362 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2014362 prefixEnd_2014362 := by exact prefixLift 2014362
  have htrace : WordTrace (prefixWord ++ tailWord_2014362) baseStart_2014362 baseEnd_2014362 := by
    simpa [prefixWord, tailWord_2014362, baseEnd_2014362] using wordTrace_append hprefix tailTrace_2014362
  have hstable : (prefixWord ++ tailWord_2014362).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2014362).length < 2 ^ (prefixWord ++ tailWord_2014362).sum := by decide
  have hdescent : baseEnd_2014362 < baseStart_2014362 := by decide
  rcases family_descends (prefixWord ++ tailWord_2014362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2014413 : List Nat := [1, 6, 2, 2, 1, 1, 1, 4, 3]
def baseStart_2014413 : Nat := 118140960795 + 2014413 * 2 ^ 59
def prefixEnd_2014413 : Nat := 4983230072969 + 3 ^ 40 * 2014413 * 2
def baseEnd_2014413 : Nat := 459716491406903259365951

theorem tailTrace_2014413 : CollatzResearch.WordTrace tailWord_2014413 prefixEnd_2014413 459716491406903259365951 := by
  unfold tailWord_2014413
  simp only [CollatzResearch.WordTrace]
  refine ⟨73471678051133210195535893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48981118700755473463690595 73471678051133210195535893)
  ·
    refine ⟨3443984908646869227915745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 73471678051133210195535893 3443984908646869227915745)
    ·
      refine ⟨2582988681485151920936809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3443984908646869227915745 2582988681485151920936809)
      ·
        refine ⟨1937241511113863940702607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2582988681485151920936809 1937241511113863940702607)
        ·
          refine ⟨2905862266670795911053911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1937241511113863940702607 2905862266670795911053911)
          ·
            refine ⟨4358793400006193866580867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2905862266670795911053911 4358793400006193866580867)
            ·
              refine ⟨6538190100009290799871301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4358793400006193866580867 6538190100009290799871301)
              ·
                refine ⟨1225910643751742024975869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6538190100009290799871301 1225910643751742024975869)
                ·
                  refine ⟨459716491406903259365951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1225910643751742024975869 459716491406903259365951)
                  ·
                    rfl

theorem cell21_2014413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 1, 4, 3].length) (baseStart_2014413 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2014413 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2014413 prefixEnd_2014413 := by exact prefixLift 2014413
  have htrace : WordTrace (prefixWord ++ tailWord_2014413) baseStart_2014413 baseEnd_2014413 := by
    simpa [prefixWord, tailWord_2014413, baseEnd_2014413] using wordTrace_append hprefix tailTrace_2014413
  have hstable : (prefixWord ++ tailWord_2014413).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2014413).length < 2 ^ (prefixWord ++ tailWord_2014413).sum := by decide
  have hdescent : baseEnd_2014413 < baseStart_2014413 := by decide
  rcases family_descends (prefixWord ++ tailWord_2014413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2014424 : List Nat := [2, 1, 2, 2, 6, 1, 1, 6]
def baseStart_2014424 : Nat := 118140960795 + 2014424 * 2 ^ 59
def prefixEnd_2014424 : Nat := 4983230072969 + 3 ^ 40 * 2014424 * 2
def baseEnd_2014424 : Nat := 153239667252256561560865

theorem tailTrace_2014424 : CollatzResearch.WordTrace tailWord_2014424 prefixEnd_2014424 153239667252256561560865 := by
  unfold tailWord_2014424
  simp only [CollatzResearch.WordTrace]
  refine ⟨36736039627046679537093163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48981386169395572716124217 36736039627046679537093163)
  ·
    refine ⟨55104059440570019305639745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36736039627046679537093163 55104059440570019305639745)
    ·
      refine ⟨41328044580427514479229809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55104059440570019305639745 41328044580427514479229809)
      ·
        refine ⟨30996033435320635859422357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41328044580427514479229809 30996033435320635859422357)
        ·
          refine ⟨1452939067280654805910423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 30996033435320635859422357 1452939067280654805910423)
          ·
            refine ⟨2179408600920982208865635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1452939067280654805910423 2179408600920982208865635)
            ·
              refine ⟨3269112901381473313298453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2179408600920982208865635 3269112901381473313298453)
              ·
                refine ⟨153239667252256561560865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3269112901381473313298453 153239667252256561560865)
                ·
                  rfl

theorem cell21_2014424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 1, 6].length) (baseStart_2014424 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2014424 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2014424 prefixEnd_2014424 := by exact prefixLift 2014424
  have htrace : WordTrace (prefixWord ++ tailWord_2014424) baseStart_2014424 baseEnd_2014424 := by
    simpa [prefixWord, tailWord_2014424, baseEnd_2014424] using wordTrace_append hprefix tailTrace_2014424
  have hstable : (prefixWord ++ tailWord_2014424).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2014424).length < 2 ^ (prefixWord ++ tailWord_2014424).sum := by decide
  have hdescent : baseEnd_2014424 < baseStart_2014424 := by decide
  rcases family_descends (prefixWord ++ tailWord_2014424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2014542 : List Nat := [4, 1, 1, 1, 1, 1, 6, 6]
def baseStart_2014542 : Nat := 118140960795 + 2014542 * 2 ^ 59
def prefixEnd_2014542 : Nat := 4983230072969 + 3 ^ 40 * 2014542 * 2
def baseEnd_2014542 : Nat := 153248643654809233905229

theorem tailTrace_2014542 : CollatzResearch.WordTrace tailWord_2014542 prefixEnd_2014542 153248643654809233905229 := by
  unfold tailWord_2014542
  simp only [CollatzResearch.WordTrace]
  refine ⟨9184547883458233153372735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48984255378443910151321253 9184547883458233153372735)
  ·
    refine ⟨13776821825187349730059103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9184547883458233153372735 13776821825187349730059103)
    ·
      refine ⟨20665232737781024595088655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13776821825187349730059103 20665232737781024595088655)
      ·
        refine ⟨30997849106671536892632983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20665232737781024595088655 30997849106671536892632983)
        ·
          refine ⟨46496773660007305338949475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30997849106671536892632983 46496773660007305338949475)
          ·
            refine ⟨69745160490010958008424213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46496773660007305338949475 69745160490010958008424213)
            ·
              refine ⟨3269304397969263656644885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 69745160490010958008424213 3269304397969263656644885)
              ·
                refine ⟨153248643654809233905229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3269304397969263656644885 153248643654809233905229)
                ·
                  rfl

theorem cell21_2014542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 6, 6].length) (baseStart_2014542 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2014542 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2014542 prefixEnd_2014542 := by exact prefixLift 2014542
  have htrace : WordTrace (prefixWord ++ tailWord_2014542) baseStart_2014542 baseEnd_2014542 := by
    simpa [prefixWord, tailWord_2014542, baseEnd_2014542] using wordTrace_append hprefix tailTrace_2014542
  have hstable : (prefixWord ++ tailWord_2014542).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2014542).length < 2 ^ (prefixWord ++ tailWord_2014542).sum := by decide
  have hdescent : baseEnd_2014542 < baseStart_2014542 := by decide
  rcases family_descends (prefixWord ++ tailWord_2014542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2014753 : List Nat := [1, 2, 3, 2, 2, 11]
def baseStart_2014753 : Nat := 118140960795 + 2014753 * 2 ^ 59
def prefixEnd_2014753 : Nat := 4983230072969 + 3 ^ 40 * 2014753 * 2
def baseEnd_2014753 : Nat := 17029410519968082359207

theorem tailTrace_2014753 : CollatzResearch.WordTrace tailWord_2014753 prefixEnd_2014753 17029410519968082359207 := by
  unfold tailWord_2014753
  simp only [CollatzResearch.WordTrace]
  refine ⟨73484078869901448262912913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48989385913267632175275275 73484078869901448262912913)
  ·
    refine ⟨55113059152426086197184685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73484078869901448262912913 55113059152426086197184685)
    ·
      refine ⟨20667397182159782323944257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55113059152426086197184685 20667397182159782323944257)
      ·
        refine ⟨15500547886619836742958193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20667397182159782323944257 15500547886619836742958193)
        ·
          refine ⟨11625410914964877557218645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15500547886619836742958193 11625410914964877557218645)
          ·
            refine ⟨17029410519968082359207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 11625410914964877557218645 17029410519968082359207)
            ·
              rfl

theorem cell21_2014753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 11].length) (baseStart_2014753 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2014753 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2014753 prefixEnd_2014753 := by exact prefixLift 2014753
  have htrace : WordTrace (prefixWord ++ tailWord_2014753) baseStart_2014753 baseEnd_2014753 := by
    simpa [prefixWord, tailWord_2014753, baseEnd_2014753] using wordTrace_append hprefix tailTrace_2014753
  have hstable : (prefixWord ++ tailWord_2014753).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2014753).length < 2 ^ (prefixWord ++ tailWord_2014753).sum := by decide
  have hdescent : baseEnd_2014753 < baseStart_2014753 := by decide
  rcases family_descends (prefixWord ++ tailWord_2014753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2014852 : List Nat := [2, 3, 2, 1, 5, 1, 1, 3, 3]
def baseStart_2014852 : Nat := 118140960795 + 2014852 * 2 ^ 59
def prefixEnd_2014852 : Nat := 4983230072969 + 3 ^ 40 * 2014852 * 2
def baseEnd_2014852 : Nat := 459816677187936051548387

theorem tailTrace_2014852 : CollatzResearch.WordTrace tailWord_2014852 prefixEnd_2014852 459816677187936051548387 := by
  unfold tailWord_2014852
  simp only [CollatzResearch.WordTrace]
  refine ⟨36743844848271394085383405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48991793131028525447177873 36743844848271394085383405)
  ·
    refine ⟨13778941818101772782018777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36743844848271394085383405 13778941818101772782018777)
    ·
      refine ⟨10334206363576329586514083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13778941818101772782018777 10334206363576329586514083)
      ·
        refine ⟨15501309545364494379771125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10334206363576329586514083 15501309545364494379771125)
        ·
          refine ⟨1453247769877921348103543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15501309545364494379771125 1453247769877921348103543)
          ·
            refine ⟨2179871654816882022155315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1453247769877921348103543 2179871654816882022155315)
            ·
              refine ⟨3269807482225323033232973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2179871654816882022155315 3269807482225323033232973)
              ·
                refine ⟨1226177805834496137462365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3269807482225323033232973 1226177805834496137462365)
                ·
                  refine ⟨459816677187936051548387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1226177805834496137462365 459816677187936051548387)
                  ·
                    rfl

theorem cell21_2014852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 1, 3, 3].length) (baseStart_2014852 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2014852 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2014852 prefixEnd_2014852 := by exact prefixLift 2014852
  have htrace : WordTrace (prefixWord ++ tailWord_2014852) baseStart_2014852 baseEnd_2014852 := by
    simpa [prefixWord, tailWord_2014852, baseEnd_2014852] using wordTrace_append hprefix tailTrace_2014852
  have hstable : (prefixWord ++ tailWord_2014852).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2014852).length < 2 ^ (prefixWord ++ tailWord_2014852).sum := by decide
  have hdescent : baseEnd_2014852 < baseStart_2014852 := by decide
  rcases family_descends (prefixWord ++ tailWord_2014852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2014905 : List Nat := [1, 2, 1, 4, 1, 1, 4, 7]
def baseStart_2014905 : Nat := 118140960795 + 2014905 * 2 ^ 59
def prefixEnd_2014905 : Nat := 4983230072969 + 3 ^ 40 * 2014905 * 2
def baseEnd_2014905 : Nat := 153276257503339912388315

theorem tailTrace_2014905 : CollatzResearch.WordTrace tailWord_2014905 prefixEnd_2014905 153276257503339912388315 := by
  unfold tailWord_2014905
  simp only [CollatzResearch.WordTrace]
  refine ⟨73489622765350778222446169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48993081843567185481630779 73489622765350778222446169)
  ·
    refine ⟨55117217074013083666834627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73489622765350778222446169 55117217074013083666834627)
    ·
      refine ⟨82675825611019625500251941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55117217074013083666834627 82675825611019625500251941)
      ·
        refine ⟨15501717302066179781297239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82675825611019625500251941 15501717302066179781297239)
        ·
          refine ⟨23252575953099269671945859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15501717302066179781297239 23252575953099269671945859)
          ·
            refine ⟨34878863929648904507918789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23252575953099269671945859 34878863929648904507918789)
            ·
              refine ⟨6539786986809169595234773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34878863929648904507918789 6539786986809169595234773)
              ·
                refine ⟨153276257503339912388315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6539786986809169595234773 153276257503339912388315)
                ·
                  rfl

theorem cell21_2014905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 4, 7].length) (baseStart_2014905 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2014905 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2014905 prefixEnd_2014905 := by exact prefixLift 2014905
  have htrace : WordTrace (prefixWord ++ tailWord_2014905) baseStart_2014905 baseEnd_2014905 := by
    simpa [prefixWord, tailWord_2014905, baseEnd_2014905] using wordTrace_append hprefix tailTrace_2014905
  have hstable : (prefixWord ++ tailWord_2014905).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2014905).length < 2 ^ (prefixWord ++ tailWord_2014905).sum := by decide
  have hdescent : baseEnd_2014905 < baseStart_2014905 := by decide
  rcases family_descends (prefixWord ++ tailWord_2014905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2014922 : List Nat := [3, 1, 2, 1, 6, 8]
def baseStart_2014922 : Nat := 118140960795 + 2014922 * 2 ^ 59
def prefixEnd_2014922 : Nat := 4983230072969 + 3 ^ 40 * 2014922 * 2
def baseEnd_2014922 : Nat := 17030838968208573532651

theorem tailTrace_2014922 : CollatzResearch.WordTrace tailWord_2014922 prefixEnd_2014922 17030838968208573532651 := by
  unfold tailWord_2014922
  simp only [CollatzResearch.WordTrace]
  refine ⟨18372560701572297531453755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48993495204192793417210013 18372560701572297531453755)
  ·
    refine ⟨27558841052358446297180633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18372560701572297531453755 27558841052358446297180633)
    ·
      refine ⟨20669130789268834722885475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27558841052358446297180633 20669130789268834722885475)
      ·
        refine ⟨31003696183903252084328213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20669130789268834722885475 31003696183903252084328213)
        ·
          refine ⟨1453298258620464941452885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 31003696183903252084328213 1453298258620464941452885)
          ·
            refine ⟨17030838968208573532651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1453298258620464941452885 17030838968208573532651)
            ·
              rfl

theorem cell21_2014922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 8].length) (baseStart_2014922 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2014922 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2014922 prefixEnd_2014922 := by exact prefixLift 2014922
  have htrace : WordTrace (prefixWord ++ tailWord_2014922) baseStart_2014922 baseEnd_2014922 := by
    simpa [prefixWord, tailWord_2014922, baseEnd_2014922] using wordTrace_append hprefix tailTrace_2014922
  have hstable : (prefixWord ++ tailWord_2014922).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2014922).length < 2 ^ (prefixWord ++ tailWord_2014922).sum := by decide
  have hdescent : baseEnd_2014922 < baseStart_2014922 := by decide
  rcases family_descends (prefixWord ++ tailWord_2014922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2014925 : List Nat := [1, 6, 2, 1, 1, 1, 1, 4, 4]
def baseStart_2014925 : Nat := 118140960795 + 2014925 * 2 ^ 59
def prefixEnd_2014925 : Nat := 4983230072969 + 3 ^ 40 * 2014925 * 2
def baseEnd_2014925 : Nat := 459833336782504146831571

theorem tailTrace_2014925 : CollatzResearch.WordTrace tailWord_2014925 prefixEnd_2014925 459833336782504146831571 := by
  unfold tailWord_2014925
  simp only [CollatzResearch.WordTrace]
  refine ⟨73490352225278321638174229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48993568150185547758782819 73490352225278321638174229)
  ·
    refine ⟨3444860260559921326789417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 73490352225278321638174229 3444860260559921326789417)
    ·
      refine ⟨2583645195419940995092063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3444860260559921326789417 2583645195419940995092063)
      ·
        refine ⟨3875467793129911492638095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2583645195419940995092063 3875467793129911492638095)
        ·
          refine ⟨5813201689694867238957143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3875467793129911492638095 5813201689694867238957143)
          ·
            refine ⟨8719802534542300858435715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5813201689694867238957143 8719802534542300858435715)
            ·
              refine ⟨13079703801813451287653573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8719802534542300858435715 13079703801813451287653573)
              ·
                refine ⟨2452444462840022116435045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13079703801813451287653573 2452444462840022116435045)
                ·
                  refine ⟨459833336782504146831571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2452444462840022116435045 459833336782504146831571)
                  ·
                    rfl

theorem cell21_2014925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 4, 4].length) (baseStart_2014925 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2014925 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2014925 prefixEnd_2014925 := by exact prefixLift 2014925
  have htrace : WordTrace (prefixWord ++ tailWord_2014925) baseStart_2014925 baseEnd_2014925 := by
    simpa [prefixWord, tailWord_2014925, baseEnd_2014925] using wordTrace_append hprefix tailTrace_2014925
  have hstable : (prefixWord ++ tailWord_2014925).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2014925).length < 2 ^ (prefixWord ++ tailWord_2014925).sum := by decide
  have hdescent : baseEnd_2014925 < baseStart_2014925 := by decide
  rcases family_descends (prefixWord ++ tailWord_2014925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2014936 : List Nat := [2, 1, 2, 2, 3, 1, 2, 3, 5]
def baseStart_2014936 : Nat := 118140960795 + 2014936 * 2 ^ 59
def prefixEnd_2014936 : Nat := 4983230072969 + 3 ^ 40 * 2014936 * 2
def baseEnd_2014936 : Nat := 459835847132370572148215

theorem tailTrace_2014936 : CollatzResearch.WordTrace tailWord_2014936 prefixEnd_2014936 459835847132370572148215 := by
  unfold tailWord_2014936
  simp only [CollatzResearch.WordTrace]
  refine ⟨36745376714119235258412331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48993835618825647011216441 36745376714119235258412331)
  ·
    refine ⟨55118065071178852887618497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36745376714119235258412331 55118065071178852887618497)
    ·
      refine ⟨41338548803384139665713873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55118065071178852887618497 41338548803384139665713873)
      ·
        refine ⟨31003911602538104749285405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41338548803384139665713873 31003911602538104749285405)
        ·
          refine ⟨11626466850951789280982027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31003911602538104749285405 11626466850951789280982027)
          ·
            refine ⟨17439700276427683921473041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11626466850951789280982027 17439700276427683921473041)
            ·
              refine ⟨13079775207320762941104781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17439700276427683921473041 13079775207320762941104781)
              ·
                refine ⟨4904915702745286102914293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13079775207320762941104781 4904915702745286102914293)
                ·
                  refine ⟨459835847132370572148215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4904915702745286102914293 459835847132370572148215)
                  ·
                    rfl

theorem cell21_2014936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 3, 5].length) (baseStart_2014936 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2014936 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2014936 prefixEnd_2014936 := by exact prefixLift 2014936
  have htrace : WordTrace (prefixWord ++ tailWord_2014936) baseStart_2014936 baseEnd_2014936 := by
    simpa [prefixWord, tailWord_2014936, baseEnd_2014936] using wordTrace_append hprefix tailTrace_2014936
  have hstable : (prefixWord ++ tailWord_2014936).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2014936).length < 2 ^ (prefixWord ++ tailWord_2014936).sum := by decide
  have hdescent : baseEnd_2014936 < baseStart_2014936 := by decide
  rcases family_descends (prefixWord ++ tailWord_2014936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2015057 : List Nat := [1, 2, 2, 1, 5, 1, 1, 8]
def baseStart_2015057 : Nat := 118140960795 + 2015057 * 2 ^ 59
def prefixEnd_2015057 : Nat := 4983230072969 + 3 ^ 40 * 2015057 * 2
def baseEnd_2015057 : Nat := 153287820326967083543767

theorem tailTrace_2015057 : CollatzResearch.WordTrace tailWord_2015057 prefixEnd_2015057 153287820326967083543767 := by
  unfold tailWord_2015057
  simp only [CollatzResearch.WordTrace]
  refine ⟨73495166660800108181979425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48996777773866738787986283 73495166660800108181979425)
  ·
    refine ⟨55121374995600081136484569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73495166660800108181979425 55121374995600081136484569)
    ·
      refine ⟨41341031246700060852363427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55121374995600081136484569 41341031246700060852363427)
      ·
        refine ⟨62011546870050091278545141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41341031246700060852363427 62011546870050091278545141)
        ·
          refine ⟨5813582519067196057363607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 62011546870050091278545141 5813582519067196057363607)
          ·
            refine ⟨8720373778600794086045411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5813582519067196057363607 8720373778600794086045411)
            ·
              refine ⟨13080560667901191129068117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8720373778600794086045411 13080560667901191129068117)
              ·
                refine ⟨153287820326967083543767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13080560667901191129068117 153287820326967083543767)
                ·
                  rfl

theorem cell21_2015057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 8].length) (baseStart_2015057 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2015057 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2015057 prefixEnd_2015057 := by exact prefixLift 2015057
  have htrace : WordTrace (prefixWord ++ tailWord_2015057) baseStart_2015057 baseEnd_2015057 := by
    simpa [prefixWord, tailWord_2015057, baseEnd_2015057] using wordTrace_append hprefix tailTrace_2015057
  have hstable : (prefixWord ++ tailWord_2015057).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2015057).length < 2 ^ (prefixWord ++ tailWord_2015057).sum := by decide
  have hdescent : baseEnd_2015057 < baseStart_2015057 := by decide
  rcases family_descends (prefixWord ++ tailWord_2015057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2015060 : List Nat := [2, 4, 1, 1, 3, 2, 1, 3, 4]
def baseStart_2015060 : Nat := 118140960795 + 2015060 * 2 ^ 59
def prefixEnd_2015060 : Nat := 4983230072969 + 3 ^ 40 * 2015060 * 2
def baseEnd_2015060 : Nat := 459864145621773912081295

theorem tailTrace_2015060 : CollatzResearch.WordTrace tailWord_2015060 prefixEnd_2015060 459864145621773912081295 := by
  unfold tailWord_2015060
  simp only [CollatzResearch.WordTrace]
  refine ⟨36747638039894619847169317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48996850719859493129559089 36747638039894619847169317)
  ·
    refine ⟨6890182132480241221344247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36747638039894619847169317 6890182132480241221344247)
    ·
      refine ⟨10335273198720361832016371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6890182132480241221344247 10335273198720361832016371)
      ·
        refine ⟨15502909798080542748024557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10335273198720361832016371 15502909798080542748024557)
        ·
          refine ⟨5813591174280203530509209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15502909798080542748024557 5813591174280203530509209)
          ·
            refine ⟨4360193380710152647881907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5813591174280203530509209 4360193380710152647881907)
            ·
              refine ⟨6540290071065228971822861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4360193380710152647881907 6540290071065228971822861)
              ·
                refine ⟨2452608776649460864433573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6540290071065228971822861 2452608776649460864433573)
                ·
                  refine ⟨459864145621773912081295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2452608776649460864433573 459864145621773912081295)
                  ·
                    rfl

theorem cell21_2015060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 1, 3, 4].length) (baseStart_2015060 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2015060 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2015060 prefixEnd_2015060 := by exact prefixLift 2015060
  have htrace : WordTrace (prefixWord ++ tailWord_2015060) baseStart_2015060 baseEnd_2015060 := by
    simpa [prefixWord, tailWord_2015060, baseEnd_2015060] using wordTrace_append hprefix tailTrace_2015060
  have hstable : (prefixWord ++ tailWord_2015060).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2015060).length < 2 ^ (prefixWord ++ tailWord_2015060).sum := by decide
  have hdescent : baseEnd_2015060 < baseStart_2015060 := by decide
  rcases family_descends (prefixWord ++ tailWord_2015060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2015074 : List Nat := [3, 3, 2, 1, 2, 1, 2, 7]
def baseStart_2015074 : Nat := 118140960795 + 2015074 * 2 ^ 59
def prefixEnd_2015074 : Nat := 4983230072969 + 3 ^ 40 * 2015074 * 2
def baseEnd_2015074 : Nat := 153289113537504332949311

theorem tailTrace_2015074 : CollatzResearch.WordTrace tailWord_2015074 prefixEnd_2015074 153289113537504332949311 := by
  unfold tailWord_2015074
  simp only [CollatzResearch.WordTrace]
  refine ⟨18373946675434630021337069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48997191134492346723565517 18373946675434630021337069)
  ·
    refine ⟨6890230003287986258001401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18373946675434630021337069 6890230003287986258001401)
    ·
      refine ⟨5167672502465989693501051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6890230003287986258001401 5167672502465989693501051)
      ·
        refine ⟨7751508753698984540251577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5167672502465989693501051 7751508753698984540251577)
        ·
          refine ⟨5813631565274238405188683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7751508753698984540251577 5813631565274238405188683)
          ·
            refine ⟨8720447347911357607783025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5813631565274238405188683 8720447347911357607783025)
            ·
              refine ⟨6540335510933518205837269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8720447347911357607783025 6540335510933518205837269)
              ·
                refine ⟨153289113537504332949311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6540335510933518205837269 153289113537504332949311)
                ·
                  rfl

theorem cell21_2015074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 2, 7].length) (baseStart_2015074 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2015074 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2015074 prefixEnd_2015074 := by exact prefixLift 2015074
  have htrace : WordTrace (prefixWord ++ tailWord_2015074) baseStart_2015074 baseEnd_2015074 := by
    simpa [prefixWord, tailWord_2015074, baseEnd_2015074] using wordTrace_append hprefix tailTrace_2015074
  have hstable : (prefixWord ++ tailWord_2015074).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2015074).length < 2 ^ (prefixWord ++ tailWord_2015074).sum := by decide
  have hdescent : baseEnd_2015074 < baseStart_2015074 := by decide
  rcases family_descends (prefixWord ++ tailWord_2015074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2015274 : List Nat := [3, 1, 4, 1, 2, 2, 1, 4, 3]
def baseStart_2015274 : Nat := 118140960795 + 2015274 * 2 ^ 59
def prefixEnd_2015274 : Nat := 4983230072969 + 3 ^ 40 * 2015274 * 2
def baseEnd_2015274 : Nat := 459912983337357095514191

theorem tailTrace_2015274 : CollatzResearch.WordTrace tailWord_2015274 prefixEnd_2015274 459912983337357095514191 := by
  unfold tailWord_2015274
  simp only [CollatzResearch.WordTrace]
  refine ⟨18375770325253488560657219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49002054200675969495085917 18375770325253488560657219)
  ·
    refine ⟨27563655487880232840985829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18375770325253488560657219 27563655487880232840985829)
    ·
      refine ⟨5168185403977543657684843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27563655487880232840985829 5168185403977543657684843)
      ·
        refine ⟨7752278105966315486527265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5168185403977543657684843 7752278105966315486527265)
        ·
          refine ⟨5814208579474736614895449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7752278105966315486527265 5814208579474736614895449)
          ·
            refine ⟨4360656434606052461171587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5814208579474736614895449 4360656434606052461171587)
            ·
              refine ⟨6540984651909078691757381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4360656434606052461171587 6540984651909078691757381)
              ·
                refine ⟨1226434622232952254704509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6540984651909078691757381 1226434622232952254704509)
                ·
                  refine ⟨459912983337357095514191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1226434622232952254704509 459912983337357095514191)
                  ·
                    rfl

theorem cell21_2015274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 1, 4, 3].length) (baseStart_2015274 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2015274 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2015274 prefixEnd_2015274 := by exact prefixLift 2015274
  have htrace : WordTrace (prefixWord ++ tailWord_2015274) baseStart_2015274 baseEnd_2015274 := by
    simpa [prefixWord, tailWord_2015274, baseEnd_2015274] using wordTrace_append hprefix tailTrace_2015274
  have hstable : (prefixWord ++ tailWord_2015274).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2015274).length < 2 ^ (prefixWord ++ tailWord_2015274).sum := by decide
  have hdescent : baseEnd_2015274 < baseStart_2015274 := by decide
  rcases family_descends (prefixWord ++ tailWord_2015274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2015285 : List Nat := [1, 3, 3, 1, 1, 1, 5, 6]
def baseStart_2015285 : Nat := 118140960795 + 2015285 * 2 ^ 59
def prefixEnd_2015285 : Nat := 4983230072969 + 3 ^ 40 * 2015285 * 2
def baseEnd_2015285 : Nat := 153305164562407840276945

theorem tailTrace_2015285 : CollatzResearch.WordTrace tailWord_2015285 prefixEnd_2015285 153305164562407840276945 := by
  unfold tailWord_2015285
  simp only [CollatzResearch.WordTrace]
  refine ⟨73503482503974103121279309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49002321669316068747519539 73503482503974103121279309)
  ·
    refine ⟨27563805938990288670479741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73503482503974103121279309 27563805938990288670479741)
    ·
      refine ⟨10336427227121358251429903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27563805938990288670479741 10336427227121358251429903)
      ·
        refine ⟨15504640840682037377144855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10336427227121358251429903 15504640840682037377144855)
        ·
          refine ⟨23256961261023056065717283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15504640840682037377144855 23256961261023056065717283)
          ·
            refine ⟨34885441891534584098575925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23256961261023056065717283 34885441891534584098575925)
            ·
              refine ⟨3270510177331367259241493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34885441891534584098575925 3270510177331367259241493)
              ·
                refine ⟨153305164562407840276945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3270510177331367259241493 153305164562407840276945)
                ·
                  rfl

theorem cell21_2015285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 5, 6].length) (baseStart_2015285 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2015285 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2015285 prefixEnd_2015285 := by exact prefixLift 2015285
  have htrace : WordTrace (prefixWord ++ tailWord_2015285) baseStart_2015285 baseEnd_2015285 := by
    simpa [prefixWord, tailWord_2015285, baseEnd_2015285] using wordTrace_append hprefix tailTrace_2015285
  have hstable : (prefixWord ++ tailWord_2015285).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2015285).length < 2 ^ (prefixWord ++ tailWord_2015285).sum := by decide
  have hdescent : baseEnd_2015285 < baseStart_2015285 := by decide
  rcases family_descends (prefixWord ++ tailWord_2015285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2015333 : List Nat := [1, 3, 1, 3, 2, 2, 2, 4, 3]
def baseStart_2015333 : Nat := 118140960795 + 2015333 * 2 ^ 59
def prefixEnd_2015333 : Nat := 4983230072969 + 3 ^ 40 * 2015333 * 2
def baseEnd_2015333 : Nat := 459926447941186104030737

theorem tailTrace_2015333 : CollatzResearch.WordTrace tailWord_2015333 prefixEnd_2015333 459926447941186104030737 := by
  unfold tailWord_2015333
  simp only [CollatzResearch.WordTrace]
  refine ⟨73505233207800207319026653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49003488805200138212684435 73505233207800207319026653)
  ·
    refine ⟨27564462452925077744634995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73505233207800207319026653 27564462452925077744634995)
    ·
      refine ⟨41346693679387616616952493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27564462452925077744634995 41346693679387616616952493)
      ·
        refine ⟨15505010129770356231357185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41346693679387616616952493 15505010129770356231357185)
        ·
          refine ⟨11628757597327767173517889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15505010129770356231357185 11628757597327767173517889)
          ·
            refine ⟨8721568197995825380138417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11628757597327767173517889 8721568197995825380138417)
            ·
              refine ⟨6541176148496869035103813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8721568197995825380138417 6541176148496869035103813)
              ·
                refine ⟨1226470527843162944081965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6541176148496869035103813 1226470527843162944081965)
                ·
                  refine ⟨459926447941186104030737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1226470527843162944081965 459926447941186104030737)
                  ·
                    rfl

theorem cell21_2015333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 2, 4, 3].length) (baseStart_2015333 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2015333 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2015333 prefixEnd_2015333 := by exact prefixLift 2015333
  have htrace : WordTrace (prefixWord ++ tailWord_2015333) baseStart_2015333 baseEnd_2015333 := by
    simpa [prefixWord, tailWord_2015333, baseEnd_2015333] using wordTrace_append hprefix tailTrace_2015333
  have hstable : (prefixWord ++ tailWord_2015333).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2015333).length < 2 ^ (prefixWord ++ tailWord_2015333).sum := by decide
  have hdescent : baseEnd_2015333 < baseStart_2015333 := by decide
  rcases family_descends (prefixWord ++ tailWord_2015333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2015392 : List Nat := [2, 1, 1, 4, 2, 2, 3, 1, 5]
def baseStart_2015392 : Nat := 118140960795 + 2015392 * 2 ^ 59
def prefixEnd_2015392 : Nat := 4983230072969 + 3 ^ 40 * 2015392 * 2
def baseEnd_2015392 : Nat := 459939912545015112547283

theorem tailTrace_2015392 : CollatzResearch.WordTrace tailWord_2015392 prefixEnd_2015392 459939912545015112547283 := by
  unfold tailWord_2015392
  simp only [CollatzResearch.WordTrace]
  refine ⟨36753692557293230197712215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49004923409724306930282953 36753692557293230197712215)
  ·
    refine ⟨55130538835939845296568323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36753692557293230197712215 55130538835939845296568323)
    ·
      refine ⟨82695808253909767944852485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55130538835939845296568323 82695808253909767944852485)
      ·
        refine ⟨15505464047608081489659841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82695808253909767944852485 15505464047608081489659841)
        ·
          refine ⟨11629098035706061117244881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15505464047608081489659841 11629098035706061117244881)
          ·
            refine ⟨8721823526779545837933661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11629098035706061117244881 8721823526779545837933661)
            ·
              refine ⟨3270683822542329689225123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8721823526779545837933661 3270683822542329689225123)
              ·
                refine ⟨4906025733813494533837685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3270683822542329689225123 4906025733813494533837685)
                ·
                  refine ⟨459939912545015112547283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4906025733813494533837685 459939912545015112547283)
                  ·
                    rfl

theorem cell21_2015392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 3, 1, 5].length) (baseStart_2015392 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2015392 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2015392 prefixEnd_2015392 := by exact prefixLift 2015392
  have htrace : WordTrace (prefixWord ++ tailWord_2015392) baseStart_2015392 baseEnd_2015392 := by
    simpa [prefixWord, tailWord_2015392, baseEnd_2015392] using wordTrace_append hprefix tailTrace_2015392
  have hstable : (prefixWord ++ tailWord_2015392).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2015392).length < 2 ^ (prefixWord ++ tailWord_2015392).sum := by decide
  have hdescent : baseEnd_2015392 < baseStart_2015392 := by decide
  rcases family_descends (prefixWord ++ tailWord_2015392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2015437 : List Nat := [1, 6, 2, 12]
def baseStart_2015437 : Nat := 118140960795 + 2015437 * 2 ^ 59
def prefixEnd_2015437 : Nat := 4983230072969 + 3 ^ 40 * 2015437 * 2
def baseEnd_2015437 : Nat := 1892799103531296437437

theorem tailTrace_2015437 : CollatzResearch.WordTrace tailWord_2015437 prefixEnd_2015437 1892799103531296437437 := by
  unfold tailWord_2015437
  simp only [CollatzResearch.WordTrace]
  refine ⟨73509026399423433080812565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49006017599615622053875043 73509026399423433080812565)
  ·
    refine ⟨3445735612472973425663089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 73509026399423433080812565 3445735612472973425663089)
    ·
      refine ⟨2584301709354730069247317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3445735612472973425663089 2584301709354730069247317)
      ·
        refine ⟨1892799103531296437437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 12 2584301709354730069247317 1892799103531296437437)
        ·
          rfl

theorem cell21_2015437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 12].length) (baseStart_2015437 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2015437 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2015437 prefixEnd_2015437 := by exact prefixLift 2015437
  have htrace : WordTrace (prefixWord ++ tailWord_2015437) baseStart_2015437 baseEnd_2015437 := by
    simpa [prefixWord, tailWord_2015437, baseEnd_2015437] using wordTrace_append hprefix tailTrace_2015437
  have hstable : (prefixWord ++ tailWord_2015437).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2015437).length < 2 ^ (prefixWord ++ tailWord_2015437).sum := by decide
  have hdescent : baseEnd_2015437 < baseStart_2015437 := by decide
  rcases family_descends (prefixWord ++ tailWord_2015437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2015530 : List Nat := [3, 1, 4, 2, 2, 1, 1, 7]
def baseStart_2015530 : Nat := 118140960795 + 2015530 * 2 ^ 59
def prefixEnd_2015530 : Nat := 4983230072969 + 3 ^ 40 * 2015530 * 2
def baseEnd_2015530 : Nat := 153323802008385846415667

theorem tailTrace_2015530 : CollatzResearch.WordTrace tailWord_2015530 prefixEnd_2015530 153323802008385846415667 := by
  unfold tailWord_2015530
  simp only [CollatzResearch.WordTrace]
  refine ⟨18378104597021627490987011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49008278925391006642632029 18378104597021627490987011)
  ·
    refine ⟨27567156895532441236480517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18378104597021627490987011 27567156895532441236480517)
    ·
      refine ⟨5168841917912332731840097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27567156895532441236480517 5168841917912332731840097)
      ·
        refine ⟨3876631438434249548880073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5168841917912332731840097 3876631438434249548880073)
        ·
          refine ⟨2907473578825687161660055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3876631438434249548880073 2907473578825687161660055)
          ·
            refine ⟨4361210368238530742490083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2907473578825687161660055 4361210368238530742490083)
            ·
              refine ⟨6541815552357796113735125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4361210368238530742490083 6541815552357796113735125)
              ·
                refine ⟨153323802008385846415667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6541815552357796113735125 153323802008385846415667)
                ·
                  rfl

theorem cell21_2015530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 1, 7].length) (baseStart_2015530 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2015530 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2015530 prefixEnd_2015530 := by exact prefixLift 2015530
  have htrace : WordTrace (prefixWord ++ tailWord_2015530) baseStart_2015530 baseEnd_2015530 := by
    simpa [prefixWord, tailWord_2015530, baseEnd_2015530] using wordTrace_append hprefix tailTrace_2015530
  have hstable : (prefixWord ++ tailWord_2015530).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2015530).length < 2 ^ (prefixWord ++ tailWord_2015530).sum := by decide
  have hdescent : baseEnd_2015530 < baseStart_2015530 := by decide
  rcases family_descends (prefixWord ++ tailWord_2015530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2015606 : List Nat := [5, 1, 1, 4, 1, 9]
def baseStart_2015606 : Nat := 118140960795 + 2015606 * 2 ^ 59
def prefixEnd_2015606 : Nat := 4983230072969 + 3 ^ 40 * 2015606 * 2
def baseEnd_2015606 : Nat := 17036620380022159110377

theorem tailTrace_2015606 : CollatzResearch.WordTrace tailWord_2015606 prefixEnd_2015606 17036620380022159110377 := by
  unfold tailWord_2015606
  simp only [CollatzResearch.WordTrace]
  refine ⟨4594699395988198433982167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 49010126890540783295809781 4594699395988198433982167)
  ·
    refine ⟨6892049093982297650973251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4594699395988198433982167 6892049093982297650973251)
    ·
      refine ⟨10338073640973446476459877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6892049093982297650973251 10338073640973446476459877)
      ·
        refine ⟨1938388807682521214336227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10338073640973446476459877 1938388807682521214336227)
        ·
          refine ⟨2907583211523781821504341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1938388807682521214336227 2907583211523781821504341)
          ·
            refine ⟨17036620380022159110377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2907583211523781821504341 17036620380022159110377)
            ·
              rfl

theorem cell21_2015606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 9].length) (baseStart_2015606 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2015606 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2015606 prefixEnd_2015606 := by exact prefixLift 2015606
  have htrace : WordTrace (prefixWord ++ tailWord_2015606) baseStart_2015606 baseEnd_2015606 := by
    simpa [prefixWord, tailWord_2015606, baseEnd_2015606] using wordTrace_append hprefix tailTrace_2015606
  have hstable : (prefixWord ++ tailWord_2015606).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2015606).length < 2 ^ (prefixWord ++ tailWord_2015606).sum := by decide
  have hdescent : baseEnd_2015606 < baseStart_2015606 := by decide
  rcases family_descends (prefixWord ++ tailWord_2015606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2015730 : List Nat := [3, 2, 1, 4, 3, 1, 1, 1, 5]
def baseStart_2015730 : Nat := 118140960795 + 2015730 * 2 ^ 59
def prefixEnd_2015730 : Nat := 4983230072969 + 3 ^ 40 * 2015730 * 2
def baseEnd_2015730 : Nat := 460017048750001635913259

theorem tailTrace_2015730 : CollatzResearch.WordTrace tailWord_2015730 prefixEnd_2015730 460017048750001635913259 := by
  unfold tailWord_2015730
  simp only [CollatzResearch.WordTrace]
  refine ⟨18379928246840486030307161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49013141991574629414152429 18379928246840486030307161)
  ·
    refine ⟨13784946185130364522730371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18379928246840486030307161 13784946185130364522730371)
    ·
      refine ⟨20677419277695546784095557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13784946185130364522730371 20677419277695546784095557)
      ·
        refine ⟨3877016114567915022017917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20677419277695546784095557 3877016114567915022017917)
        ·
          refine ⟨1453881042962968133256719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3877016114567915022017917 1453881042962968133256719)
          ·
            refine ⟨2180821564444452199885079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1453881042962968133256719 2180821564444452199885079)
            ·
              refine ⟨3271232346666678299827619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2180821564444452199885079 3271232346666678299827619)
              ·
                refine ⟨4906848520000017449741429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3271232346666678299827619 4906848520000017449741429)
                ·
                  refine ⟨460017048750001635913259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4906848520000017449741429 460017048750001635913259)
                  ·
                    rfl

theorem cell21_2015730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 1, 1, 5].length) (baseStart_2015730 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2015730 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2015730 prefixEnd_2015730 := by exact prefixLift 2015730
  have htrace : WordTrace (prefixWord ++ tailWord_2015730) baseStart_2015730 baseEnd_2015730 := by
    simpa [prefixWord, tailWord_2015730, baseEnd_2015730] using wordTrace_append hprefix tailTrace_2015730
  have hstable : (prefixWord ++ tailWord_2015730).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2015730).length < 2 ^ (prefixWord ++ tailWord_2015730).sum := by decide
  have hdescent : baseEnd_2015730 < baseStart_2015730 := by decide
  rcases family_descends (prefixWord ++ tailWord_2015730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2015882 : List Nat := [3, 1, 2, 3, 3, 2, 1, 3, 3]
def baseStart_2015882 : Nat := 118140960795 + 2015882 * 2 ^ 59
def prefixEnd_2015882 : Nat := 4983230072969 + 3 ^ 40 * 2015882 * 2
def baseEnd_2015882 : Nat := 460051737220883149379615

theorem tailTrace_2015882 : CollatzResearch.WordTrace tailWord_2015882 prefixEnd_2015882 460051737220883149379615 := by
  unfold tailWord_2015882
  simp only [CollatzResearch.WordTrace]
  refine ⟨18381314220702818520190475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49016837921874182720507933 18381314220702818520190475)
  ·
    refine ⟨27571971331054227780285713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18381314220702818520190475 27571971331054227780285713)
    ·
      refine ⟨20678978498290670835214285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27571971331054227780285713 20678978498290670835214285)
      ·
        refine ⟨7754616936859001563205357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20678978498290670835214285 7754616936859001563205357)
        ·
          refine ⟨2907981351322125586202009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7754616936859001563205357 2907981351322125586202009)
          ·
            refine ⟨2180986013491594189651507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2907981351322125586202009 2180986013491594189651507)
            ·
              refine ⟨3271479020237391284477261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2180986013491594189651507 3271479020237391284477261)
              ·
                refine ⟨1226804632589021731678973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3271479020237391284477261 1226804632589021731678973)
                ·
                  refine ⟨460051737220883149379615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1226804632589021731678973 460051737220883149379615)
                  ·
                    rfl

theorem cell21_2015882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 1, 3, 3].length) (baseStart_2015882 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2015882 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2015882 prefixEnd_2015882 := by exact prefixLift 2015882
  have htrace : WordTrace (prefixWord ++ tailWord_2015882) baseStart_2015882 baseEnd_2015882 := by
    simpa [prefixWord, tailWord_2015882, baseEnd_2015882] using wordTrace_append hprefix tailTrace_2015882
  have hstable : (prefixWord ++ tailWord_2015882).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2015882).length < 2 ^ (prefixWord ++ tailWord_2015882).sum := by decide
  have hdescent : baseEnd_2015882 < baseStart_2015882 := by decide
  rcases family_descends (prefixWord ++ tailWord_2015882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2015969 : List Nat := [1, 2, 3, 1, 4, 3, 1, 6]
def baseStart_2015969 : Nat := 118140960795 + 2015969 * 2 ^ 59
def prefixEnd_2015969 : Nat := 4983230072969 + 3 ^ 40 * 2015969 * 2
def baseEnd_2015969 : Nat := 153357197268730110476479

theorem tailTrace_2015969 : CollatzResearch.WordTrace tailWord_2015969 prefixEnd_2015969 153357197268730110476479 := by
  unfold tailWord_2015969
  simp only [CollatzResearch.WordTrace]
  refine ⟨73528430033496087939178961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49018953355664058626119307 73528430033496087939178961)
  ·
    refine ⟨55146322525122065954384221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73528430033496087939178961 55146322525122065954384221)
    ·
      refine ⟨20679870946920774732894083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55146322525122065954384221 20679870946920774732894083)
      ·
        refine ⟨31019806420381162099341125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20679870946920774732894083 31019806420381162099341125)
        ·
          refine ⟨5816213703821467893626461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31019806420381162099341125 5816213703821467893626461)
          ·
            refine ⟨2181080138933050460109923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5816213703821467893626461 2181080138933050460109923)
            ·
              refine ⟨3271620208399575690164885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2181080138933050460109923 3271620208399575690164885)
              ·
                refine ⟨153357197268730110476479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3271620208399575690164885 153357197268730110476479)
                ·
                  rfl

theorem cell21_2015969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 1, 6].length) (baseStart_2015969 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2015969 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2015969 prefixEnd_2015969 := by exact prefixLift 2015969
  have htrace : WordTrace (prefixWord ++ tailWord_2015969) baseStart_2015969 baseEnd_2015969 := by
    simpa [prefixWord, tailWord_2015969, baseEnd_2015969] using wordTrace_append hprefix tailTrace_2015969
  have hstable : (prefixWord ++ tailWord_2015969).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2015969).length < 2 ^ (prefixWord ++ tailWord_2015969).sum := by decide
  have hdescent : baseEnd_2015969 < baseStart_2015969 := by decide
  rcases family_descends (prefixWord ++ tailWord_2015969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2015983 : List Nat := [1, 1, 2, 1, 5, 3, 1, 2, 5]
def baseStart_2015983 : Nat := 118140960795 + 2015983 * 2 ^ 59
def prefixEnd_2015983 : Nat := 4983230072969 + 3 ^ 40 * 2015983 * 2
def baseEnd_2015983 : Nat := 460074786796929418196075

theorem tailTrace_2015983 : CollatzResearch.WordTrace tailWord_2015983 prefixEnd_2015983 460074786796929418196075 := by
  unfold tailWord_2015983
  simp only [CollatzResearch.WordTrace]
  refine ⟨73528940655445368330188603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49019293770296912220125735 73528940655445368330188603)
  ·
    refine ⟨110293410983168052495282905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73528940655445368330188603 110293410983168052495282905)
    ·
      refine ⟨82720058237376039371462179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110293410983168052495282905 82720058237376039371462179)
      ·
        refine ⟨124080087356064059057193269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82720058237376039371462179 124080087356064059057193269)
        ·
          refine ⟨11632508189631005536611869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 124080087356064059057193269 11632508189631005536611869)
          ·
            refine ⟨4362190571111627076229451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11632508189631005536611869 4362190571111627076229451)
            ·
              refine ⟨6543285856667440614344177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4362190571111627076229451 6543285856667440614344177)
              ·
                refine ⟨4907464392500580460758133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6543285856667440614344177 4907464392500580460758133)
                ·
                  refine ⟨460074786796929418196075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4907464392500580460758133 460074786796929418196075)
                  ·
                    rfl

theorem cell21_2015983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 1, 2, 5].length) (baseStart_2015983 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2015983 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2015983 prefixEnd_2015983 := by exact prefixLift 2015983
  have htrace : WordTrace (prefixWord ++ tailWord_2015983) baseStart_2015983 baseEnd_2015983 := by
    simpa [prefixWord, tailWord_2015983, baseEnd_2015983] using wordTrace_append hprefix tailTrace_2015983
  have hstable : (prefixWord ++ tailWord_2015983).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2015983).length < 2 ^ (prefixWord ++ tailWord_2015983).sum := by decide
  have hdescent : baseEnd_2015983 < baseStart_2015983 := by decide
  rcases family_descends (prefixWord ++ tailWord_2015983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2015997 : List Nat := [1, 4, 1, 1, 1, 1, 4, 2, 6]
def baseStart_2015997 : Nat := 118140960795 + 2015997 * 2 ^ 59
def prefixEnd_2015997 : Nat := 4983230072969 + 3 ^ 40 * 2015997 * 2
def baseEnd_2015997 : Nat := 460077981787668504962713

theorem tailTrace_2015997 : CollatzResearch.WordTrace tailWord_2015997 prefixEnd_2015997 460077981787668504962713 := by
  unfold tailWord_2015997
  simp only [CollatzResearch.WordTrace]
  refine ⟨73529451277394648721198245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49019634184929765814132163 73529451277394648721198245)
  ·
    refine ⟨13786772114511496635224671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73529451277394648721198245 13786772114511496635224671)
    ·
      refine ⟨20680158171767244952837007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13786772114511496635224671 20680158171767244952837007)
      ·
        refine ⟨31020237257650867429255511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20680158171767244952837007 31020237257650867429255511)
        ·
          refine ⟨46530355886476301143883267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31020237257650867429255511 46530355886476301143883267)
          ·
            refine ⟨69795533829714451715824901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46530355886476301143883267 69795533829714451715824901)
            ·
              refine ⟨13086662593071459696717169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69795533829714451715824901 13086662593071459696717169)
              ·
                refine ⟨9814996944803594772537877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13086662593071459696717169 9814996944803594772537877)
                ·
                  refine ⟨460077981787668504962713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9814996944803594772537877 460077981787668504962713)
                  ·
                    rfl

theorem cell21_2015997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 2, 6].length) (baseStart_2015997 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2015997 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2015997 prefixEnd_2015997 := by exact prefixLift 2015997
  have htrace : WordTrace (prefixWord ++ tailWord_2015997) baseStart_2015997 baseEnd_2015997 := by
    simpa [prefixWord, tailWord_2015997, baseEnd_2015997] using wordTrace_append hprefix tailTrace_2015997
  have hstable : (prefixWord ++ tailWord_2015997).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2015997).length < 2 ^ (prefixWord ++ tailWord_2015997).sum := by decide
  have hdescent : baseEnd_2015997 < baseStart_2015997 := by decide
  rcases family_descends (prefixWord ++ tailWord_2015997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2016031 : List Nat := [1, 1, 2, 4, 2, 3, 3, 1, 4]
def baseStart_2016031 : Nat := 118140960795 + 2016031 * 2 ^ 59
def prefixEnd_2016031 : Nat := 4983230072969 + 3 ^ 40 * 2016031 * 2
def baseEnd_2016031 : Nat := 460085741050892001395977

theorem tailTrace_2016031 : CollatzResearch.WordTrace tailWord_2016031 prefixEnd_2016031 460085741050892001395977 := by
  unfold tailWord_2016031
  simp only [CollatzResearch.WordTrace]
  refine ⟨73530691359271472527935947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49020460906180981685290631 73530691359271472527935947)
  ·
    refine ⟨110296037038907208791903921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73530691359271472527935947 110296037038907208791903921)
    ·
      refine ⟨82722027779180406593927941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110296037038907208791903921 82722027779180406593927941)
      ·
        refine ⟨15510380208596326236361489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82722027779180406593927941 15510380208596326236361489)
        ·
          refine ⟨11632785156447244677271117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15510380208596326236361489 11632785156447244677271117)
          ·
            refine ⟨4362294433667716753976669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11632785156447244677271117 4362294433667716753976669)
            ·
              refine ⟨1635860412625393782741251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4362294433667716753976669 1635860412625393782741251)
              ·
                refine ⟨2453790618938090674111877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1635860412625393782741251 2453790618938090674111877)
                ·
                  refine ⟨460085741050892001395977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2453790618938090674111877 460085741050892001395977)
                  ·
                    rfl

theorem cell21_2016031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 3, 1, 4].length) (baseStart_2016031 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2016031 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2016031 prefixEnd_2016031 := by exact prefixLift 2016031
  have htrace : WordTrace (prefixWord ++ tailWord_2016031) baseStart_2016031 baseEnd_2016031 := by
    simpa [prefixWord, tailWord_2016031, baseEnd_2016031] using wordTrace_append hprefix tailTrace_2016031
  have hstable : (prefixWord ++ tailWord_2016031).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2016031).length < 2 ^ (prefixWord ++ tailWord_2016031).sum := by decide
  have hdescent : baseEnd_2016031 < baseStart_2016031 := by decide
  rcases family_descends (prefixWord ++ tailWord_2016031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2016062 : List Nat := [4, 2, 1, 2, 4, 1, 7]
def baseStart_2016062 : Nat := 118140960795 + 2016062 * 2 ^ 59
def prefixEnd_2016062 : Nat := 4983230072969 + 3 ^ 40 * 2016062 * 2
def baseEnd_2016062 : Nat := 51121423963693648486583

theorem tailTrace_2016062 : CollatzResearch.WordTrace tailWord_2016062 prefixEnd_2016062 51121423963693648486583 := by
  unfold tailWord_2016062
  simp only [CollatzResearch.WordTrace]
  refine ⟨9191477752769895602789305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49021214681439443214876293 9191477752769895602789305)
  ·
    refine ⟨6893608314577421702091979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9191477752769895602789305 6893608314577421702091979)
    ·
      refine ⟨10340412471866132553137969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6893608314577421702091979 10340412471866132553137969)
      ·
        refine ⟨7755309353899599414853477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10340412471866132553137969 7755309353899599414853477)
        ·
          refine ⟨1454120503856174890285027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7755309353899599414853477 1454120503856174890285027)
          ·
            refine ⟨2181180755784262335427541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1454120503856174890285027 2181180755784262335427541)
            ·
              refine ⟨51121423963693648486583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2181180755784262335427541 51121423963693648486583)
              ·
                rfl

theorem cell21_2016062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 7].length) (baseStart_2016062 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2016062 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2016062 prefixEnd_2016062 := by exact prefixLift 2016062
  have htrace : WordTrace (prefixWord ++ tailWord_2016062) baseStart_2016062 baseEnd_2016062 := by
    simpa [prefixWord, tailWord_2016062, baseEnd_2016062] using wordTrace_append hprefix tailTrace_2016062
  have hstable : (prefixWord ++ tailWord_2016062).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2016062).length < 2 ^ (prefixWord ++ tailWord_2016062).sum := by decide
  have hdescent : baseEnd_2016062 < baseStart_2016062 := by decide
  rcases family_descends (prefixWord ++ tailWord_2016062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2016073 : List Nat := [1, 2, 1, 1, 2, 5, 2, 1, 6]
def baseStart_2016073 : Nat := 118140960795 + 2016073 * 2 ^ 59
def prefixEnd_2016073 : Nat := 4983230072969 + 3 ^ 40 * 2016073 * 2
def baseEnd_2016073 : Nat := 460095326023109261695891

theorem tailTrace_2016073 : CollatzResearch.WordTrace tailWord_2016073 prefixEnd_2016073 460095326023109261695891 := by
  unfold tailWord_2016073
  simp only [CollatzResearch.WordTrace]
  refine ⟨73532223225119313700964873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49021482150079542467309915 73532223225119313700964873)
  ·
    refine ⟨55149167418839485275723655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73532223225119313700964873 55149167418839485275723655)
    ·
      refine ⟨82723751128259227913585483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55149167418839485275723655 82723751128259227913585483)
      ·
        refine ⟨124085626692388841870378225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82723751128259227913585483 124085626692388841870378225)
        ·
          refine ⟨93064220019291631402783669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124085626692388841870378225 93064220019291631402783669)
          ·
            refine ⟨8724770626808590444010969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 93064220019291631402783669 8724770626808590444010969)
            ·
              refine ⟨6543577970106442833008227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8724770626808590444010969 6543577970106442833008227)
              ·
                refine ⟨9815366955159664249512341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6543577970106442833008227 9815366955159664249512341)
                ·
                  refine ⟨460095326023109261695891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9815366955159664249512341 460095326023109261695891)
                  ·
                    rfl

theorem cell21_2016073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 2, 1, 6].length) (baseStart_2016073 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2016073 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2016073 prefixEnd_2016073 := by exact prefixLift 2016073
  have htrace : WordTrace (prefixWord ++ tailWord_2016073) baseStart_2016073 baseEnd_2016073 := by
    simpa [prefixWord, tailWord_2016073, baseEnd_2016073] using wordTrace_append hprefix tailTrace_2016073
  have hstable : (prefixWord ++ tailWord_2016073).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2016073).length < 2 ^ (prefixWord ++ tailWord_2016073).sum := by decide
  have hdescent : baseEnd_2016073 < baseStart_2016073 := by decide
  rcases family_descends (prefixWord ++ tailWord_2016073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2016076 : List Nat := [2, 2, 1, 3, 3, 3, 1, 1, 5]
def baseStart_2016076 : Nat := 118140960795 + 2016076 * 2 ^ 59
def prefixEnd_2016076 : Nat := 4983230072969 + 3 ^ 40 * 2016076 * 2
def baseEnd_2016076 : Nat := 460096010663981923145885

theorem tailTrace_2016076 : CollatzResearch.WordTrace tailWord_2016076 prefixEnd_2016076 460096010663981923145885 := by
  unfold tailWord_2016076
  simp only [CollatzResearch.WordTrace]
  refine ⟨36766166322054222606662041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49021555096072296808882721 36766166322054222606662041)
  ·
    refine ⟨27574624741540666954996531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36766166322054222606662041 27574624741540666954996531)
    ·
      refine ⟨41361937112311000432494797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27574624741540666954996531 41361937112311000432494797)
      ·
        refine ⟨15510726417116625162185549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41361937112311000432494797 15510726417116625162185549)
        ·
          refine ⟨5816522406418734435819581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15510726417116625162185549 5816522406418734435819581)
          ·
            refine ⟨2181195902407025413432343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5816522406418734435819581 2181195902407025413432343)
            ·
              refine ⟨3271793853610538120148515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2181195902407025413432343 3271793853610538120148515)
              ·
                refine ⟨4907690780415807180222773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3271793853610538120148515 4907690780415807180222773)
                ·
                  refine ⟨460096010663981923145885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4907690780415807180222773 460096010663981923145885)
                  ·
                    rfl

theorem cell21_2016076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 1, 1, 5].length) (baseStart_2016076 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2016076 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2016076 prefixEnd_2016076 := by exact prefixLift 2016076
  have htrace : WordTrace (prefixWord ++ tailWord_2016076) baseStart_2016076 baseEnd_2016076 := by
    simpa [prefixWord, tailWord_2016076, baseEnd_2016076] using wordTrace_append hprefix tailTrace_2016076
  have hstable : (prefixWord ++ tailWord_2016076).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2016076).length < 2 ^ (prefixWord ++ tailWord_2016076).sum := by decide
  have hdescent : baseEnd_2016076 < baseStart_2016076 := by decide
  rcases family_descends (prefixWord ++ tailWord_2016076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2016090 : List Nat := [3, 1, 1, 2, 1, 5, 1, 3, 4]
def baseStart_2016090 : Nat := 118140960795 + 2016090 * 2 ^ 59
def prefixEnd_2016090 : Nat := 4983230072969 + 3 ^ 40 * 2016090 * 2
def baseEnd_2016090 : Nat := 460099205654721009912523

theorem tailTrace_2016090 : CollatzResearch.WordTrace tailWord_2016090 prefixEnd_2016090 460099205654721009912523 := by
  unfold tailWord_2016090
  simp only [CollatzResearch.WordTrace]
  refine ⟨18383210816514431401083431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49021895510705150402889149 18383210816514431401083431)
  ·
    refine ⟨27574816224771647101625147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18383210816514431401083431 27574816224771647101625147)
    ·
      refine ⟨41362224337157470652437721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27574816224771647101625147 41362224337157470652437721)
      ·
        refine ⟨31021668252868102989328291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41362224337157470652437721 31021668252868102989328291)
        ·
          refine ⟨46532502379302154483992437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31021668252868102989328291 46532502379302154483992437)
          ·
            refine ⟨4362422098059576982874291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 46532502379302154483992437 4362422098059576982874291)
            ·
              refine ⟨6543633147089365474311437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4362422098059576982874291 6543633147089365474311437)
              ·
                refine ⟨2453862430158512052866789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6543633147089365474311437 2453862430158512052866789)
                ·
                  refine ⟨460099205654721009912523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2453862430158512052866789 460099205654721009912523)
                  ·
                    rfl

theorem cell21_2016090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 1, 3, 4].length) (baseStart_2016090 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2016090 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2016090 prefixEnd_2016090 := by exact prefixLift 2016090
  have htrace : WordTrace (prefixWord ++ tailWord_2016090) baseStart_2016090 baseEnd_2016090 := by
    simpa [prefixWord, tailWord_2016090, baseEnd_2016090] using wordTrace_append hprefix tailTrace_2016090
  have hstable : (prefixWord ++ tailWord_2016090).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2016090).length < 2 ^ (prefixWord ++ tailWord_2016090).sum := by decide
  have hdescent : baseEnd_2016090 < baseStart_2016090 := by decide
  rcases family_descends (prefixWord ++ tailWord_2016090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2016104 : List Nat := [2, 1, 4, 2, 1, 2, 2, 7]
def baseStart_2016104 : Nat := 118140960795 + 2016104 * 2 ^ 59
def prefixEnd_2016104 : Nat := 4983230072969 + 3 ^ 40 * 2016104 * 2
def baseEnd_2016104 : Nat := 153367466881820032226387

theorem tailTrace_2016104 : CollatzResearch.WordTrace tailWord_2016104 prefixEnd_2016104 153367466881820032226387 := by
  unfold tailWord_2016104
  simp only [CollatzResearch.WordTrace]
  refine ⟨36766676944003502997671683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49022235925338003996895577 36766676944003502997671683)
  ·
    refine ⟨55150015416005254496507525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36766676944003502997671683 55150015416005254496507525)
    ·
      refine ⟨10340627890500985218095161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55150015416005254496507525 10340627890500985218095161)
      ·
        refine ⟨7755470917875738913571371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10340627890500985218095161 7755470917875738913571371)
        ·
          refine ⟨11633206376813608370357057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7755470917875738913571371 11633206376813608370357057)
          ·
            refine ⟨8724904782610206277767793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11633206376813608370357057 8724904782610206277767793)
            ·
              refine ⟨6543678586957654708325845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8724904782610206277767793 6543678586957654708325845)
              ·
                refine ⟨153367466881820032226387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6543678586957654708325845 153367466881820032226387)
                ·
                  rfl

theorem cell21_2016104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 2, 7].length) (baseStart_2016104 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2016104 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2016104 prefixEnd_2016104 := by exact prefixLift 2016104
  have htrace : WordTrace (prefixWord ++ tailWord_2016104) baseStart_2016104 baseEnd_2016104 := by
    simpa [prefixWord, tailWord_2016104, baseEnd_2016104] using wordTrace_append hprefix tailTrace_2016104
  have hstable : (prefixWord ++ tailWord_2016104).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2016104).length < 2 ^ (prefixWord ++ tailWord_2016104).sum := by decide
  have hdescent : baseEnd_2016104 < baseStart_2016104 := by decide
  rcases family_descends (prefixWord ++ tailWord_2016104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2016163 : List Nat := [1, 1, 1, 4, 1, 2, 2, 9]
def baseStart_2016163 : Nat := 118140960795 + 2016163 * 2 ^ 59
def prefixEnd_2016163 : Nat := 4983230072969 + 3 ^ 40 * 2016163 * 2
def baseEnd_2016163 : Nat := 153371955083096368398569

theorem tailTrace_2016163 : CollatzResearch.WordTrace tailWord_2016163 prefixEnd_2016163 153371955083096368398569 := by
  unfold tailWord_2016163
  simp only [CollatzResearch.WordTrace]
  refine ⟨73535505794793259071741143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49023670529862172714494095 73535505794793259071741143)
  ·
    refine ⟨110303258692189888607611715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73535505794793259071741143 110303258692189888607611715)
    ·
      refine ⟨165454888038284832911417573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110303258692189888607611715 165454888038284832911417573)
      ·
        refine ⟨31022791507178406170890795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 165454888038284832911417573 31022791507178406170890795)
        ·
          refine ⟨46534187260767609256336193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31022791507178406170890795 46534187260767609256336193)
          ·
            refine ⟨34900640445575706942252145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46534187260767609256336193 34900640445575706942252145)
            ·
              refine ⟨26175480334181780206689109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34900640445575706942252145 26175480334181780206689109)
              ·
                refine ⟨153371955083096368398569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 26175480334181780206689109 153371955083096368398569)
                ·
                  rfl

theorem cell21_2016163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 9].length) (baseStart_2016163 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2016163 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2016163 prefixEnd_2016163 := by exact prefixLift 2016163
  have htrace : WordTrace (prefixWord ++ tailWord_2016163) baseStart_2016163 baseEnd_2016163 := by
    simpa [prefixWord, tailWord_2016163, baseEnd_2016163] using wordTrace_append hprefix tailTrace_2016163
  have hstable : (prefixWord ++ tailWord_2016163).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2016163).length < 2 ^ (prefixWord ++ tailWord_2016163).sum := by decide
  have hdescent : baseEnd_2016163 < baseStart_2016163 := by decide
  rcases family_descends (prefixWord ++ tailWord_2016163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2016214 : List Nat := [5, 2, 1, 1, 2, 1, 4, 5]
def baseStart_2016214 : Nat := 118140960795 + 2016214 * 2 ^ 59
def prefixEnd_2016214 : Nat := 4983230072969 + 3 ^ 40 * 2016214 * 2
def baseEnd_2016214 : Nat := 153375834714708116615201

theorem tailTrace_2016214 : CollatzResearch.WordTrace tailWord_2016214 prefixEnd_2016214 153375834714708116615201 := by
  unfold tailWord_2016214
  simp only [CollatzResearch.WordTrace]
  refine ⟨4596085369850530923865481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 49024910611738996521231797 4596085369850530923865481)
  ·
    refine ⟨3447064027387898192899111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4596085369850530923865481 3447064027387898192899111)
    ·
      refine ⟨5170596041081847289348667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3447064027387898192899111 5170596041081847289348667)
      ·
        refine ⟨7755894061622770934023001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5170596041081847289348667 7755894061622770934023001)
        ·
          refine ⟨5816920546217078200517251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7755894061622770934023001 5816920546217078200517251)
          ·
            refine ⟨8725380819325617300775877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5816920546217078200517251 8725380819325617300775877)
            ·
              refine ⟨1636008903623553243895477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8725380819325617300775877 1636008903623553243895477)
              ·
                refine ⟨153375834714708116615201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1636008903623553243895477 153375834714708116615201)
                ·
                  rfl

theorem cell21_2016214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 4, 5].length) (baseStart_2016214 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2016214 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2016214 prefixEnd_2016214 := by exact prefixLift 2016214
  have htrace : WordTrace (prefixWord ++ tailWord_2016214) baseStart_2016214 baseEnd_2016214 := by
    simpa [prefixWord, tailWord_2016214, baseEnd_2016214] using wordTrace_append hprefix tailTrace_2016214
  have hstable : (prefixWord ++ tailWord_2016214).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2016214).length < 2 ^ (prefixWord ++ tailWord_2016214).sum := by decide
  have hdescent : baseEnd_2016214 < baseStart_2016214 := by decide
  rcases family_descends (prefixWord ++ tailWord_2016214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2016239 : List Nat := [1, 1, 2, 1, 4, 3, 9]
def baseStart_2016239 : Nat := 118140960795 + 2016239 * 2 ^ 59
def prefixEnd_2016239 : Nat := 4983230072969 + 3 ^ 40 * 2016239 * 2
def baseEnd_2016239 : Nat := 51125912164969984658765

theorem tailTrace_2016239 : CollatzResearch.WordTrace tailWord_2016239 prefixEnd_2016239 51125912164969984658765 := by
  unfold tailWord_2016239
  simp only [CollatzResearch.WordTrace]
  refine ⟨73538277742517924051507771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49025518495011949367671847 73538277742517924051507771)
  ·
    refine ⟨110307416613776886077261657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73538277742517924051507771 110307416613776886077261657)
    ·
      refine ⟨82730562460332664557946243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110307416613776886077261657 82730562460332664557946243)
      ·
        refine ⟨124095843690498996836919365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82730562460332664557946243 124095843690498996836919365)
        ·
          refine ⟨23267970691968561906922381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 124095843690498996836919365 23267970691968561906922381)
          ·
            refine ⟨8725489009488210715095893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23267970691968561906922381 8725489009488210715095893)
            ·
              refine ⟨51125912164969984658765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8725489009488210715095893 51125912164969984658765)
              ·
                rfl

theorem cell21_2016239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 9].length) (baseStart_2016239 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2016239 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2016239 prefixEnd_2016239 := by exact prefixLift 2016239
  have htrace : WordTrace (prefixWord ++ tailWord_2016239) baseStart_2016239 baseEnd_2016239 := by
    simpa [prefixWord, tailWord_2016239, baseEnd_2016239] using wordTrace_append hprefix tailTrace_2016239
  have hstable : (prefixWord ++ tailWord_2016239).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2016239).length < 2 ^ (prefixWord ++ tailWord_2016239).sum := by decide
  have hdescent : baseEnd_2016239 < baseStart_2016239 := by decide
  rcases family_descends (prefixWord ++ tailWord_2016239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2016349 : List Nat := [1, 4, 4, 1, 2, 1, 8]
def baseStart_2016349 : Nat := 118140960795 + 2016349 * 2 ^ 59
def prefixEnd_2016349 : Nat := 4983230072969 + 3 ^ 40 * 2016349 * 2
def baseEnd_2016349 : Nat := 51128701442599346121703

theorem tailTrace_2016349 : CollatzResearch.WordTrace tailWord_2016349 prefixEnd_2016349 51128701442599346121703 := by
  unfold tailWord_2016349
  simp only [CollatzResearch.WordTrace]
  refine ⟨73542289772119412838012101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49028193181412941892008067 73542289772119412838012101)
  ·
    refine ⟨13789179332272389907127269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73542289772119412838012101 13789179332272389907127269)
    ·
      refine ⟨2585471124801073107586363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13789179332272389907127269 2585471124801073107586363)
      ·
        refine ⟨3878206687201609661379545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2585471124801073107586363 3878206687201609661379545)
        ·
          refine ⟨2908655015401207246034659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3878206687201609661379545 2908655015401207246034659)
          ·
            refine ⟨4362982523101810869051989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2908655015401207246034659 4362982523101810869051989)
            ·
              refine ⟨51128701442599346121703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4362982523101810869051989 51128701442599346121703)
              ·
                rfl

theorem cell21_2016349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 8].length) (baseStart_2016349 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2016349 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2016349 prefixEnd_2016349 := by exact prefixLift 2016349
  have htrace : WordTrace (prefixWord ++ tailWord_2016349) baseStart_2016349 baseEnd_2016349 := by
    simpa [prefixWord, tailWord_2016349, baseEnd_2016349] using wordTrace_append hprefix tailTrace_2016349
  have hstable : (prefixWord ++ tailWord_2016349).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2016349).length < 2 ^ (prefixWord ++ tailWord_2016349).sum := by decide
  have hdescent : baseEnd_2016349 < baseStart_2016349 := by decide
  rcases family_descends (prefixWord ++ tailWord_2016349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2016408 : List Nat := [2, 1, 2, 4, 2, 3, 7]
def baseStart_2016408 : Nat := 118140960795 + 2016408 * 2 ^ 59
def prefixEnd_2016408 : Nat := 4983230072969 + 3 ^ 40 * 2016408 * 2
def baseEnd_2016408 : Nat := 51130197509691458179097

theorem tailTrace_2016408 : CollatzResearch.WordTrace tailWord_2016408 prefixEnd_2016408 51130197509691458179097 := by
  unfold tailWord_2016408
  simp only [CollatzResearch.WordTrace]
  refine ⟨36772220839452832957204939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49029627785937110609606585 36772220839452832957204939)
  ·
    refine ⟨55158331259179249435807409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36772220839452832957204939 55158331259179249435807409)
    ·
      refine ⟨41368748444384437076855557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55158331259179249435807409 41368748444384437076855557)
      ·
        refine ⟨7756640333322081951910417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41368748444384437076855557 7756640333322081951910417)
        ·
          refine ⟨5817480249991561463932813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7756640333322081951910417 5817480249991561463932813)
          ·
            refine ⟨2181555093746835548974805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5817480249991561463932813 2181555093746835548974805)
            ·
              refine ⟨51130197509691458179097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2181555093746835548974805 51130197509691458179097)
              ·
                rfl

theorem cell21_2016408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 7].length) (baseStart_2016408 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2016408 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2016408 prefixEnd_2016408 := by exact prefixLift 2016408
  have htrace : WordTrace (prefixWord ++ tailWord_2016408) baseStart_2016408 baseEnd_2016408 := by
    simpa [prefixWord, tailWord_2016408, baseEnd_2016408] using wordTrace_append hprefix tailTrace_2016408
  have hstable : (prefixWord ++ tailWord_2016408).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2016408).length < 2 ^ (prefixWord ++ tailWord_2016408).sum := by decide
  have hdescent : baseEnd_2016408 < baseStart_2016408 := by decide
  rcases family_descends (prefixWord ++ tailWord_2016408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2016414 : List Nat := [4, 3, 1, 1, 2, 2, 3, 2, 3]
def baseStart_2016414 : Nat := 118140960795 + 2016414 * 2 ^ 59
def prefixEnd_2016414 : Nat := 4983230072969 + 3 ^ 40 * 2016414 * 2
def baseEnd_2016414 : Nat := 460173146868968446511861

theorem tailTrace_2016414 : CollatzResearch.WordTrace tailWord_2016414 prefixEnd_2016414 460173146868968446511861 := by
  unfold tailWord_2016414
  simp only [CollatzResearch.WordTrace]
  refine ⟨9193082564610491117391037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49029773677922619292752197 9193082564610491117391037)
  ·
    refine ⟨3447405961728934169021639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9193082564610491117391037 3447405961728934169021639)
    ·
      refine ⟨5171108942593401253532459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3447405961728934169021639 5171108942593401253532459)
      ·
        refine ⟨7756663413890101880298689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5171108942593401253532459 7756663413890101880298689)
        ·
          refine ⟨5817497560417576410224017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7756663413890101880298689 5817497560417576410224017)
          ·
            refine ⟨4363123170313182307668013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5817497560417576410224017 4363123170313182307668013)
            ·
              refine ⟨1636171188867443365375505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4363123170313182307668013 1636171188867443365375505)
              ·
                refine ⟨1227128391650582524031629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1636171188867443365375505 1227128391650582524031629)
                ·
                  refine ⟨460173146868968446511861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1227128391650582524031629 460173146868968446511861)
                  ·
                    rfl

theorem cell21_2016414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 3, 2, 3].length) (baseStart_2016414 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2016414 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2016414 prefixEnd_2016414 := by exact prefixLift 2016414
  have htrace : WordTrace (prefixWord ++ tailWord_2016414) baseStart_2016414 baseEnd_2016414 := by
    simpa [prefixWord, tailWord_2016414, baseEnd_2016414] using wordTrace_append hprefix tailTrace_2016414
  have hstable : (prefixWord ++ tailWord_2016414).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2016414).length < 2 ^ (prefixWord ++ tailWord_2016414).sum := by decide
  have hdescent : baseEnd_2016414 < baseStart_2016414 := by decide
  rcases family_descends (prefixWord ++ tailWord_2016414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2016512 : List Nat := [2, 1, 1, 2, 1, 1, 3, 4, 6]
def baseStart_2016512 : Nat := 118140960795 + 2016512 * 2 ^ 59
def prefixEnd_2016512 : Nat := 4983230072969 + 3 ^ 40 * 2016512 * 2
def baseEnd_2016512 : Nat := 460195511804142053878327

theorem tailTrace_2016512 : CollatzResearch.WordTrace tailWord_2016512 prefixEnd_2016512 460195511804142053878327 := by
  unfold tailWord_2016512
  simp only [CollatzResearch.WordTrace]
  refine ⟨36774117435264445838097895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49032156580352594450797193 36774117435264445838097895)
  ·
    refine ⟨55161176152896668757146843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36774117435264445838097895 55161176152896668757146843)
    ·
      refine ⟨82741764229345003135720265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55161176152896668757146843 82741764229345003135720265)
      ·
        refine ⟨62056323172008752351790199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82741764229345003135720265 62056323172008752351790199)
        ·
          refine ⟨93084484758013128527685299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62056323172008752351790199 93084484758013128527685299)
          ·
            refine ⟨139626727137019692791527949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93084484758013128527685299 139626727137019692791527949)
            ·
              refine ⟨52360022676382384796822981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 139626727137019692791527949 52360022676382384796822981)
              ·
                refine ⟨9817504251821697149404309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52360022676382384796822981 9817504251821697149404309)
                ·
                  refine ⟨460195511804142053878327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9817504251821697149404309 460195511804142053878327)
                  ·
                    rfl

theorem cell21_2016512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 4, 6].length) (baseStart_2016512 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2016512 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2016512 prefixEnd_2016512 := by exact prefixLift 2016512
  have htrace : WordTrace (prefixWord ++ tailWord_2016512) baseStart_2016512 baseEnd_2016512 := by
    simpa [prefixWord, tailWord_2016512, baseEnd_2016512] using wordTrace_append hprefix tailTrace_2016512
  have hstable : (prefixWord ++ tailWord_2016512).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2016512).length < 2 ^ (prefixWord ++ tailWord_2016512).sum := by decide
  have hdescent : baseEnd_2016512 < baseStart_2016512 := by decide
  rcases family_descends (prefixWord ++ tailWord_2016512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2016515 : List Nat := [1, 1, 1, 3, 2, 4, 1, 5, 3]
def baseStart_2016515 : Nat := 118140960795 + 2016515 * 2 ^ 59
def prefixEnd_2016515 : Nat := 4983230072969 + 3 ^ 40 * 2016515 * 2
def baseEnd_2016515 : Nat := 460196196445014715328321

theorem tailTrace_2016515 : CollatzResearch.WordTrace tailWord_2016515 prefixEnd_2016515 460196196445014715328321 := by
  unfold tailWord_2016515
  simp only [CollatzResearch.WordTrace]
  refine ⟨73548344289518023188554999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49032229526345348792369999 73548344289518023188554999)
  ·
    refine ⟨110322516434277034782832499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73548344289518023188554999 110322516434277034782832499)
    ·
      refine ⟨165483774651415552174248749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110322516434277034782832499 165483774651415552174248749)
      ·
        refine ⟨62056415494280832065343281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 165483774651415552174248749 62056415494280832065343281)
        ·
          refine ⟨46542311620710624049007461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62056415494280832065343281 46542311620710624049007461)
          ·
            refine ⟨8726683428883242009188899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46542311620710624049007461 8726683428883242009188899)
            ·
              refine ⟨13090025143324863013783349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8726683428883242009188899 13090025143324863013783349)
              ·
                refine ⟨1227189857186705907542189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13090025143324863013783349 1227189857186705907542189)
                ·
                  refine ⟨460196196445014715328321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1227189857186705907542189 460196196445014715328321)
                  ·
                    rfl

theorem cell21_2016515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 5, 3].length) (baseStart_2016515 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2016515 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2016515 prefixEnd_2016515 := by exact prefixLift 2016515
  have htrace : WordTrace (prefixWord ++ tailWord_2016515) baseStart_2016515 baseEnd_2016515 := by
    simpa [prefixWord, tailWord_2016515, baseEnd_2016515] using wordTrace_append hprefix tailTrace_2016515
  have hstable : (prefixWord ++ tailWord_2016515).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2016515).length < 2 ^ (prefixWord ++ tailWord_2016515).sum := by decide
  have hdescent : baseEnd_2016515 < baseStart_2016515 := by decide
  rcases family_descends (prefixWord ++ tailWord_2016515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2016642 : List Nat := [3, 4, 2, 1, 1, 1, 4, 2, 3]
def baseStart_2016642 : Nat := 118140960795 + 2016642 * 2 ^ 59
def prefixEnd_2016642 : Nat := 4983230072969 + 3 ^ 40 * 2016642 * 2
def baseEnd_2016642 : Nat := 460225179575290716711395

theorem tailTrace_2016642 : CollatzResearch.WordTrace tailWord_2016642 prefixEnd_2016642 460225179575290716711395 := by
  unfold tailWord_2016642
  simp only [CollatzResearch.WordTrace]
  refine ⟨18388244090014480969607045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49035317573371949252285453 18388244090014480969607045)
  ·
    refine ⟨3447795766877715181801321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18388244090014480969607045 3447795766877715181801321)
    ·
      refine ⟨2585846825158286386350991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3447795766877715181801321 2585846825158286386350991)
      ·
        refine ⟨3878770237737429579526487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2585846825158286386350991 3878770237737429579526487)
        ·
          refine ⟨5818155356606144369289731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3878770237737429579526487 5818155356606144369289731)
          ·
            refine ⟨8727233034909216553934597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5818155356606144369289731 8727233034909216553934597)
            ·
              refine ⟨1636356194045478103862737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8727233034909216553934597 1636356194045478103862737)
              ·
                refine ⟨1227267145534108577897053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1636356194045478103862737 1227267145534108577897053)
                ·
                  refine ⟨460225179575290716711395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1227267145534108577897053 460225179575290716711395)
                  ·
                    rfl

theorem cell21_2016642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 4, 2, 3].length) (baseStart_2016642 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2016642 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2016642 prefixEnd_2016642 := by exact prefixLift 2016642
  have htrace : WordTrace (prefixWord ++ tailWord_2016642) baseStart_2016642 baseEnd_2016642 := by
    simpa [prefixWord, tailWord_2016642, baseEnd_2016642] using wordTrace_append hprefix tailTrace_2016642
  have hstable : (prefixWord ++ tailWord_2016642).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2016642).length < 2 ^ (prefixWord ++ tailWord_2016642).sum := by decide
  have hdescent : baseEnd_2016642 < baseStart_2016642 := by decide
  rcases family_descends (prefixWord ++ tailWord_2016642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2016670 : List Nat := [4, 3, 1, 2, 2, 1, 3, 5]
def baseStart_2016670 : Nat := 118140960795 + 2016670 * 2 ^ 59
def prefixEnd_2016670 : Nat := 4983230072969 + 3 ^ 40 * 2016670 * 2
def baseEnd_2016670 : Nat := 153410523185589630081557

theorem tailTrace_2016670 : CollatzResearch.WordTrace tailWord_2016670 prefixEnd_2016670 153410523185589630081557 := by
  unfold tailWord_2016670
  simp only [CollatzResearch.WordTrace]
  refine ⟨9194249700494560582555933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49035998402637656440298309 9194249700494560582555933)
  ·
    refine ⟨3447843637685460218458475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9194249700494560582555933 3447843637685460218458475)
    ·
      refine ⟨5171765456528190327687713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3447843637685460218458475 5171765456528190327687713)
      ·
        refine ⟨3878824092396142745765785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5171765456528190327687713 3878824092396142745765785)
        ·
          refine ⟨2909118069297107059324339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3878824092396142745765785 2909118069297107059324339)
          ·
            refine ⟨4363677103945660588986509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2909118069297107059324339 4363677103945660588986509)
            ·
              refine ⟨1636378913979622720869941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4363677103945660588986509 1636378913979622720869941)
              ·
                refine ⟨153410523185589630081557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1636378913979622720869941 153410523185589630081557)
                ·
                  rfl

theorem cell21_2016670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 3, 5].length) (baseStart_2016670 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2016670 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2016670 prefixEnd_2016670 := by exact prefixLift 2016670
  have htrace : WordTrace (prefixWord ++ tailWord_2016670) baseStart_2016670 baseEnd_2016670 := by
    simpa [prefixWord, tailWord_2016670, baseEnd_2016670] using wordTrace_append hprefix tailTrace_2016670
  have hstable : (prefixWord ++ tailWord_2016670).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2016670).length < 2 ^ (prefixWord ++ tailWord_2016670).sum := by decide
  have hdescent : baseEnd_2016670 < baseStart_2016670 := by decide
  rcases family_descends (prefixWord ++ tailWord_2016670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2016760 : List Nat := [2, 1, 2, 1, 1, 6, 3, 2, 3]
def baseStart_2016760 : Nat := 118140960795 + 2016760 * 2 ^ 59
def prefixEnd_2016760 : Nat := 4983230072969 + 3 ^ 40 * 2016760 * 2
def baseEnd_2016760 : Nat := 460252108782948733744487

theorem tailTrace_2016760 : CollatzResearch.WordTrace tailWord_2016760 prefixEnd_2016760 460252108782948733744487 := by
  unfold tailWord_2016760
  simp only [CollatzResearch.WordTrace]
  refine ⟨36778640086815215015611867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49038186782420286687482489 36778640086815215015611867)
  ·
    refine ⟨55167960130222822523417801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36778640086815215015611867 55167960130222822523417801)
    ·
      refine ⟨41375970097667116892563351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55167960130222822523417801 41375970097667116892563351)
      ·
        refine ⟨62063955146500675338845027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41375970097667116892563351 62063955146500675338845027)
        ·
          refine ⟨93095932719751013008267541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62063955146500675338845027 93095932719751013008267541)
          ·
            refine ⟨4363871846238328734762541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 93095932719751013008267541 4363871846238328734762541)
            ·
              refine ⟨1636451942339373275535953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4363871846238328734762541 1636451942339373275535953)
              ·
                refine ⟨1227338956754529956651965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1636451942339373275535953 1227338956754529956651965)
                ·
                  refine ⟨460252108782948733744487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1227338956754529956651965 460252108782948733744487)
                  ·
                    rfl

theorem cell21_2016760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 3, 2, 3].length) (baseStart_2016760 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2016760 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2016760 prefixEnd_2016760 := by exact prefixLift 2016760
  have htrace : WordTrace (prefixWord ++ tailWord_2016760) baseStart_2016760 baseEnd_2016760 := by
    simpa [prefixWord, tailWord_2016760, baseEnd_2016760] using wordTrace_append hprefix tailTrace_2016760
  have hstable : (prefixWord ++ tailWord_2016760).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2016760).length < 2 ^ (prefixWord ++ tailWord_2016760).sum := by decide
  have hdescent : baseEnd_2016760 < baseStart_2016760 := by decide
  rcases family_descends (prefixWord ++ tailWord_2016760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2016785 : List Nat := [1, 2, 2, 1, 1, 2, 4, 1, 7]
def baseStart_2016785 : Nat := 118140960795 + 2016785 * 2 ^ 59
def prefixEnd_2016785 : Nat := 4983230072969 + 3 ^ 40 * 2016785 * 2
def baseEnd_2016785 : Nat := 460257814123554245827769

theorem tailTrace_2016785 : CollatzResearch.WordTrace tailWord_2016785 prefixEnd_2016785 460257814123554245827769 := by
  unfold tailWord_2016785
  simp only [CollatzResearch.WordTrace]
  refine ⟨73558191998539859300883809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49038794665693239533922539 73558191998539859300883809)
  ·
    refine ⟨55168643998904894475662857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73558191998539859300883809 55168643998904894475662857)
    ·
      refine ⟨41376482999178670856747143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55168643998904894475662857 41376482999178670856747143)
      ·
        refine ⟨62064724498768006285120715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41376482999178670856747143 62064724498768006285120715)
        ·
          refine ⟨93097086748152009427681073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62064724498768006285120715 93097086748152009427681073)
          ·
            refine ⟨69822815061114007070760805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93097086748152009427681073 69822815061114007070760805)
            ·
              refine ⟨13091777823958876325767651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69822815061114007070760805 13091777823958876325767651)
              ·
                refine ⟨19637666735938314488651477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13091777823958876325767651 19637666735938314488651477)
                ·
                  refine ⟨460257814123554245827769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19637666735938314488651477 460257814123554245827769)
                  ·
                    rfl

theorem cell21_2016785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 1, 7].length) (baseStart_2016785 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2016785 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2016785 prefixEnd_2016785 := by exact prefixLift 2016785
  have htrace : WordTrace (prefixWord ++ tailWord_2016785) baseStart_2016785 baseEnd_2016785 := by
    simpa [prefixWord, tailWord_2016785, baseEnd_2016785] using wordTrace_append hprefix tailTrace_2016785
  have hstable : (prefixWord ++ tailWord_2016785).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2016785).length < 2 ^ (prefixWord ++ tailWord_2016785).sum := by decide
  have hdescent : baseEnd_2016785 < baseStart_2016785 := by decide
  rcases family_descends (prefixWord ++ tailWord_2016785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2016819 : List Nat := [1, 1, 1, 2, 4, 4, 1, 4, 3]
def baseStart_2016819 : Nat := 118140960795 + 2016819 * 2 ^ 59
def prefixEnd_2016819 : Nat := 4983230072969 + 3 ^ 40 * 2016819 * 2
def baseEnd_2016819 : Nat := 460265573386777742261033

theorem tailTrace_2016819 : CollatzResearch.WordTrace tailWord_2016819 prefixEnd_2016819 460265573386777742261033 := by
  unfold tailWord_2016819
  simp only [CollatzResearch.WordTrace]
  refine ⟨73559432080416683107621511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49039621386944455405081007 73559432080416683107621511)
  ·
    refine ⟨110339148120625024661432267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73559432080416683107621511 110339148120625024661432267)
    ·
      refine ⟨165508722180937536992148401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110339148120625024661432267 165508722180937536992148401)
      ·
        refine ⟨124131541635703152744111301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165508722180937536992148401 124131541635703152744111301)
        ·
          refine ⟨23274664056694341139520869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 124131541635703152744111301 23274664056694341139520869)
          ·
            refine ⟨4363999510630188963660163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23274664056694341139520869 4363999510630188963660163)
            ·
              refine ⟨6545999265945283445490245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4363999510630188963660163 6545999265945283445490245)
              ·
                refine ⟨1227374862364740646029421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6545999265945283445490245 1227374862364740646029421)
                ·
                  refine ⟨460265573386777742261033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1227374862364740646029421 460265573386777742261033)
                  ·
                    rfl

theorem cell21_2016819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 1, 4, 3].length) (baseStart_2016819 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2016819 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2016819 prefixEnd_2016819 := by exact prefixLift 2016819
  have htrace : WordTrace (prefixWord ++ tailWord_2016819) baseStart_2016819 baseEnd_2016819 := by
    simpa [prefixWord, tailWord_2016819, baseEnd_2016819] using wordTrace_append hprefix tailTrace_2016819
  have hstable : (prefixWord ++ tailWord_2016819).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2016819).length < 2 ^ (prefixWord ++ tailWord_2016819).sum := by decide
  have hdescent : baseEnd_2016819 < baseStart_2016819 := by decide
  rcases family_descends (prefixWord ++ tailWord_2016819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2016822 : List Nat := [5, 1, 2, 1, 4, 1, 1, 6]
def baseStart_2016822 : Nat := 118140960795 + 2016822 * 2 ^ 59
def prefixEnd_2016822 : Nat := 4983230072969 + 3 ^ 40 * 2016822 * 2
def baseEnd_2016822 : Nat := 153422086009216801237009

theorem tailTrace_2016822 : CollatzResearch.WordTrace tailWord_2016822 prefixEnd_2016822 153422086009216801237009 := by
  unfold tailWord_2016822
  simp only [CollatzResearch.WordTrace]
  refine ⟨4597471343712863413748795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 49039694332937209746653813 4597471343712863413748795)
  ·
    refine ⟨6896207015569295120623193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4597471343712863413748795 6896207015569295120623193)
    ·
      refine ⟨5172155261676971340467395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6896207015569295120623193 5172155261676971340467395)
      ·
        refine ⟨7758232892515457010701093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5172155261676971340467395 7758232892515457010701093)
        ·
          refine ⟨1454668667346648189506455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7758232892515457010701093 1454668667346648189506455)
          ·
            refine ⟨2182003001019972284259683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1454668667346648189506455 2182003001019972284259683)
            ·
              refine ⟨3273004501529958426389525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2182003001019972284259683 3273004501529958426389525)
              ·
                refine ⟨153422086009216801237009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3273004501529958426389525 153422086009216801237009)
                ·
                  rfl

theorem cell21_2016822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 1, 6].length) (baseStart_2016822 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2016822 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2016822 prefixEnd_2016822 := by exact prefixLift 2016822
  have htrace : WordTrace (prefixWord ++ tailWord_2016822) baseStart_2016822 baseEnd_2016822 := by
    simpa [prefixWord, tailWord_2016822, baseEnd_2016822] using wordTrace_append hprefix tailTrace_2016822
  have hstable : (prefixWord ++ tailWord_2016822).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2016822).length < 2 ^ (prefixWord ++ tailWord_2016822).sum := by decide
  have hdescent : baseEnd_2016822 < baseStart_2016822 := by decide
  rcases family_descends (prefixWord ++ tailWord_2016822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2016833 : List Nat := [1, 2, 5, 1, 1, 1, 1, 5, 4]
def baseStart_2016833 : Nat := 118140960795 + 2016833 * 2 ^ 59
def prefixEnd_2016833 : Nat := 4983230072969 + 3 ^ 40 * 2016833 * 2
def baseEnd_2016833 : Nat := 460268768377516829027671

theorem tailTrace_2016833 : CollatzResearch.WordTrace tailWord_2016833 prefixEnd_2016833 460268768377516829027671 := by
  unfold tailWord_2016833
  simp only [CollatzResearch.WordTrace]
  refine ⟨73559942702365963498631153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49039961801577308999087435 73559942702365963498631153)
  ·
    refine ⟨55169957026774472623973365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73559942702365963498631153 55169957026774472623973365)
    ·
      refine ⟨5172183471260106808497503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 55169957026774472623973365 5172183471260106808497503)
      ·
        refine ⟨7758275206890160212746255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5172183471260106808497503 7758275206890160212746255)
        ·
          refine ⟨11637412810335240319119383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7758275206890160212746255 11637412810335240319119383)
          ·
            refine ⟨17456119215502860478679075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11637412810335240319119383 17456119215502860478679075)
            ·
              refine ⟨26184178823254290718018613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17456119215502860478679075 26184178823254290718018613)
              ·
                refine ⟨2454766764680089754814245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26184178823254290718018613 2454766764680089754814245)
                ·
                  refine ⟨460268768377516829027671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2454766764680089754814245 460268768377516829027671)
                  ·
                    rfl

theorem cell21_2016833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 5, 4].length) (baseStart_2016833 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2016833 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2016833 prefixEnd_2016833 := by exact prefixLift 2016833
  have htrace : WordTrace (prefixWord ++ tailWord_2016833) baseStart_2016833 baseEnd_2016833 := by
    simpa [prefixWord, tailWord_2016833, baseEnd_2016833] using wordTrace_append hprefix tailTrace_2016833
  have hstable : (prefixWord ++ tailWord_2016833).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2016833).length < 2 ^ (prefixWord ++ tailWord_2016833).sum := by decide
  have hdescent : baseEnd_2016833 < baseStart_2016833 := by decide
  rcases family_descends (prefixWord ++ tailWord_2016833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2016985 : List Nat := [1, 2, 1, 2, 3, 4, 2, 2, 4]
def baseStart_2016985 : Nat := 118140960795 + 2016985 * 2 ^ 59
def prefixEnd_2016985 : Nat := 4983230072969 + 3 ^ 40 * 2016985 * 2
def baseEnd_2016985 : Nat := 460303456848398342494027

theorem tailTrace_2016985 : CollatzResearch.WordTrace tailWord_2016985 prefixEnd_2016985 460303456848398342494027 := by
  unfold tailWord_2016985
  simp only [CollatzResearch.WordTrace]
  refine ⟨73565486597815293458164409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49043657731876862305442939 73565486597815293458164409)
  ·
    refine ⟨55174114948361470093623307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73565486597815293458164409 55174114948361470093623307)
    ·
      refine ⟨82761172422542205140434961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55174114948361470093623307 82761172422542205140434961)
      ·
        refine ⟨62070879316906653855326221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82761172422542205140434961 62070879316906653855326221)
        ·
          refine ⟨23276579743839995195747333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62070879316906653855326221 23276579743839995195747333)
          ·
            refine ⟨4364358701969999099202625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23276579743839995195747333 4364358701969999099202625)
            ·
              refine ⟨3273269026477499324401969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4364358701969999099202625 3273269026477499324401969)
              ·
                refine ⟨2454951769858124493301477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3273269026477499324401969 2454951769858124493301477)
                ·
                  refine ⟨460303456848398342494027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2454951769858124493301477 460303456848398342494027)
                  ·
                    rfl

theorem cell21_2016985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 2, 2, 4].length) (baseStart_2016985 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2016985 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2016985 prefixEnd_2016985 := by exact prefixLift 2016985
  have htrace : WordTrace (prefixWord ++ tailWord_2016985) baseStart_2016985 baseEnd_2016985 := by
    simpa [prefixWord, tailWord_2016985, baseEnd_2016985] using wordTrace_append hprefix tailTrace_2016985
  have hstable : (prefixWord ++ tailWord_2016985).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2016985).length < 2 ^ (prefixWord ++ tailWord_2016985).sum := by decide
  have hdescent : baseEnd_2016985 < baseStart_2016985 := by decide
  rcases family_descends (prefixWord ++ tailWord_2016985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2017047 : List Nat := [1, 1, 3, 4, 2, 1, 2, 4, 3]
def baseStart_2017047 : Nat := 118140960795 + 2017047 * 2 ^ 59
def prefixEnd_2017047 : Nat := 4983230072969 + 3 ^ 40 * 2017047 * 2
def baseEnd_2017047 : Nat := 460317606093100012460567

theorem tailTrace_2017047 : CollatzResearch.WordTrace tailWord_2017047 prefixEnd_2017047 460317606093100012460567 := by
  unfold tailWord_2017047
  simp only [CollatzResearch.WordTrace]
  refine ⟨73567747923590678046921395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49045165282393785364614263 73567747923590678046921395)
  ·
    refine ⟨110351621885386017070382093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73567747923590678046921395 110351621885386017070382093)
    ·
      refine ⟨41381858207019756401393285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110351621885386017070382093 41381858207019756401393285)
      ·
        refine ⟨7759098413816204325261241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41381858207019756401393285 7759098413816204325261241)
        ·
          refine ⟨5819323810362153243945931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7759098413816204325261241 5819323810362153243945931)
          ·
            refine ⟨8728985715543229865918897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5819323810362153243945931 8728985715543229865918897)
            ·
              refine ⟨6546739286657422399439173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8728985715543229865918897 6546739286657422399439173)
              ·
                refine ⟨1227513616248266699894845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6546739286657422399439173 1227513616248266699894845)
                ·
                  refine ⟨460317606093100012460567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1227513616248266699894845 460317606093100012460567)
                  ·
                    rfl

theorem cell21_2017047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 2, 4, 3].length) (baseStart_2017047 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2017047 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2017047 prefixEnd_2017047 := by exact prefixLift 2017047
  have htrace : WordTrace (prefixWord ++ tailWord_2017047) baseStart_2017047 baseEnd_2017047 := by
    simpa [prefixWord, tailWord_2017047, baseEnd_2017047] using wordTrace_append hprefix tailTrace_2017047
  have hstable : (prefixWord ++ tailWord_2017047).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2017047).length < 2 ^ (prefixWord ++ tailWord_2017047).sum := by decide
  have hdescent : baseEnd_2017047 < baseStart_2017047 := by decide
  rcases family_descends (prefixWord ++ tailWord_2017047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2017075 : List Nat := [1, 1, 1, 2, 7, 1, 1, 7]
def baseStart_2017075 : Nat := 118140960795 + 2017075 * 2 ^ 59
def prefixEnd_2017075 : Nat := 4983230072969 + 3 ^ 40 * 2017075 * 2
def baseEnd_2017075 : Nat := 153441332024859395331281

theorem tailTrace_2017075 : CollatzResearch.WordTrace tailWord_2017075 prefixEnd_2017075 153441332024859395331281 := by
  unfold tailWord_2017075
  simp only [CollatzResearch.WordTrace]
  refine ⟨73568769167489238828940679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49045846111659492552627119 73568769167489238828940679)
  ·
    refine ⟨110353153751233858243411019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73568769167489238828940679 110353153751233858243411019)
    ·
      refine ⟨165529730626850787365116529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110353153751233858243411019 165529730626850787365116529)
      ·
        refine ⟨124147297970138090523837397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165529730626850787365116529 124147297970138090523837397)
        ·
          refine ⟨2909702296175111496652439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 124147297970138090523837397 2909702296175111496652439)
          ·
            refine ⟨4364553444262667244978659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2909702296175111496652439 4364553444262667244978659)
            ·
              refine ⟨6546830166394000867467989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4364553444262667244978659 6546830166394000867467989)
              ·
                refine ⟨153441332024859395331281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6546830166394000867467989 153441332024859395331281)
                ·
                  rfl

theorem cell21_2017075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 1, 7].length) (baseStart_2017075 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2017075 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2017075 prefixEnd_2017075 := by exact prefixLift 2017075
  have htrace : WordTrace (prefixWord ++ tailWord_2017075) baseStart_2017075 baseEnd_2017075 := by
    simpa [prefixWord, tailWord_2017075, baseEnd_2017075] using wordTrace_append hprefix tailTrace_2017075
  have hstable : (prefixWord ++ tailWord_2017075).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2017075).length < 2 ^ (prefixWord ++ tailWord_2017075).sum := by decide
  have hdescent : baseEnd_2017075 < baseStart_2017075 := by decide
  rcases family_descends (prefixWord ++ tailWord_2017075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2017081 : List Nat := [1, 2, 1, 7, 1, 2, 1, 3, 3]
def baseStart_2017081 : Nat := 118140960795 + 2017081 * 2 ^ 59
def prefixEnd_2017081 : Nat := 4983230072969 + 3 ^ 40 * 2017081 * 2
def baseEnd_2017081 : Nat := 460325365356323508893831

theorem tailTrace_2017081 : CollatzResearch.WordTrace tailWord_2017081 prefixEnd_2017081 460325365356323508893831 := by
  unfold tailWord_2017081
  simp only [CollatzResearch.WordTrace]
  refine ⟨73568988005467501853659097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49045992003645001235772731 73568988005467501853659097)
  ·
    refine ⟨55176741004100626390244323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73568988005467501853659097 55176741004100626390244323)
    ·
      refine ⟨82765111506150939585366485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55176741004100626390244323 82765111506150939585366485)
      ·
        refine ⟨1939807300925412646532027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 82765111506150939585366485 1939807300925412646532027)
        ·
          refine ⟨2909710951388118969798041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1939807300925412646532027 2909710951388118969798041)
          ·
            refine ⟨2182283213541089227348531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2909710951388118969798041 2182283213541089227348531)
            ·
              refine ⟨3273424820311633841022797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2182283213541089227348531 3273424820311633841022797)
              ·
                refine ⟨1227534307616862690383549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3273424820311633841022797 1227534307616862690383549)
                ·
                  refine ⟨460325365356323508893831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1227534307616862690383549 460325365356323508893831)
                  ·
                    rfl

theorem cell21_2017081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 1, 3, 3].length) (baseStart_2017081 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2017081 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2017081 prefixEnd_2017081 := by exact prefixLift 2017081
  have htrace : WordTrace (prefixWord ++ tailWord_2017081) baseStart_2017081 baseEnd_2017081 := by
    simpa [prefixWord, tailWord_2017081, baseEnd_2017081] using wordTrace_append hprefix tailTrace_2017081
  have hstable : (prefixWord ++ tailWord_2017081).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2017081).length < 2 ^ (prefixWord ++ tailWord_2017081).sum := by decide
  have hdescent : baseEnd_2017081 < baseStart_2017081 := by decide
  rcases family_descends (prefixWord ++ tailWord_2017081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2017106 : List Nat := [3, 2, 2, 1, 1, 3, 3, 1, 5]
def baseStart_2017106 : Nat := 118140960795 + 2017106 * 2 ^ 59
def prefixEnd_2017106 : Nat := 4983230072969 + 3 ^ 40 * 2017106 * 2
def baseEnd_2017106 : Nat := 460331070696929020977113

theorem tailTrace_2017106 : CollatzResearch.WordTrace tailWord_2017106 prefixEnd_2017106 460331070696929020977113 := by
  unfold tailWord_2017106
  simp only [CollatzResearch.WordTrace]
  refine ⟨18392474957594232780829793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49046599886917954082212781 18392474957594232780829793)
  ·
    refine ⟨13794356218195674585622345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18392474957594232780829793 13794356218195674585622345)
    ·
      refine ⟨10345767163646755939216759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13794356218195674585622345 10345767163646755939216759)
      ·
        refine ⟨15518650745470133908825139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10345767163646755939216759 15518650745470133908825139)
        ·
          refine ⟨23277976118205200863237709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15518650745470133908825139 23277976118205200863237709)
          ·
            refine ⟨8729241044326950323714141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23277976118205200863237709 8729241044326950323714141)
            ·
              refine ⟨3273465391622606371392803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8729241044326950323714141 3273465391622606371392803)
              ·
                refine ⟨4910198087433909557089205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3273465391622606371392803 4910198087433909557089205)
                ·
                  refine ⟨460331070696929020977113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4910198087433909557089205 460331070696929020977113)
                  ·
                    rfl

theorem cell21_2017106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 3, 1, 5].length) (baseStart_2017106 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2017106 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2017106 prefixEnd_2017106 := by exact prefixLift 2017106
  have htrace : WordTrace (prefixWord ++ tailWord_2017106) baseStart_2017106 baseEnd_2017106 := by
    simpa [prefixWord, tailWord_2017106, baseEnd_2017106] using wordTrace_append hprefix tailTrace_2017106
  have hstable : (prefixWord ++ tailWord_2017106).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2017106).length < 2 ^ (prefixWord ++ tailWord_2017106).sum := by decide
  have hdescent : baseEnd_2017106 < baseStart_2017106 := by decide
  rcases family_descends (prefixWord ++ tailWord_2017106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2017213 : List Nat := [1, 4, 1, 2, 3, 1, 3, 2, 4]
def baseStart_2017213 : Nat := 118140960795 + 2017213 * 2 ^ 59
def prefixEnd_2017213 : Nat := 4983230072969 + 3 ^ 40 * 2017213 * 2
def baseEnd_2017213 : Nat := 460355489554720612693561

theorem tailTrace_2017213 : CollatzResearch.WordTrace tailWord_2017213 prefixEnd_2017213 460355489554720612693561 := by
  unfold tailWord_2017213
  simp only [CollatzResearch.WordTrace]
  refine ⟨73573802440989288397464293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49049201627326192264976195 73573802440989288397464293)
  ·
    refine ⟨13795087957685491574524555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73573802440989288397464293 13795087957685491574524555)
    ·
      refine ⟨20692631936528237361786833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13795087957685491574524555 20692631936528237361786833)
      ·
        refine ⟨15519473952396178021340125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20692631936528237361786833 15519473952396178021340125)
        ·
          refine ⟨5819802732148566758002547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15519473952396178021340125 5819802732148566758002547)
          ·
            refine ⟨8729704098222850137003821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5819802732148566758002547 8729704098222850137003821)
            ·
              refine ⟨3273639036833568801376433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8729704098222850137003821 3273639036833568801376433)
              ·
                refine ⟨2455229277625176601032325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3273639036833568801376433 2455229277625176601032325)
                ·
                  refine ⟨460355489554720612693561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2455229277625176601032325 460355489554720612693561)
                  ·
                    rfl

theorem cell21_2017213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 3, 2, 4].length) (baseStart_2017213 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2017213 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2017213 prefixEnd_2017213 := by exact prefixLift 2017213
  have htrace : WordTrace (prefixWord ++ tailWord_2017213) baseStart_2017213 baseEnd_2017213 := by
    simpa [prefixWord, tailWord_2017213, baseEnd_2017213] using wordTrace_append hprefix tailTrace_2017213
  have hstable : (prefixWord ++ tailWord_2017213).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2017213).length < 2 ^ (prefixWord ++ tailWord_2017213).sum := by decide
  have hdescent : baseEnd_2017213 < baseStart_2017213 := by decide
  rcases family_descends (prefixWord ++ tailWord_2017213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2017250 : List Nat := [3, 3, 3, 1, 3, 1, 1, 3, 3]
def baseStart_2017250 : Nat := 118140960795 + 2017250 * 2 ^ 59
def prefixEnd_2017250 : Nat := 4983230072969 + 3 ^ 40 * 2017250 * 2
def baseEnd_2017250 : Nat := 460363933458816770576819

theorem tailTrace_2017250 : CollatzResearch.WordTrace tailWord_2017250 prefixEnd_2017250 460363933458816770576819 := by
  unfold tailWord_2017250
  simp only [CollatzResearch.WordTrace]
  refine ⟨18393787985463810929140301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49050101294570162477707469 18393787985463810929140301)
  ·
    refine ⟨6897670494548929098427613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18393787985463810929140301 6897670494548929098427613)
    ·
      refine ⟨2586626435455848411910355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6897670494548929098427613 2586626435455848411910355)
      ·
        refine ⟨3879939653183772617865533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2586626435455848411910355 3879939653183772617865533)
        ·
          refine ⟨1454977369943914731699575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3879939653183772617865533 1454977369943914731699575)
          ·
            refine ⟨2182466054915872097549363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1454977369943914731699575 2182466054915872097549363)
            ·
              refine ⟨3273699082373808146324045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2182466054915872097549363 3273699082373808146324045)
              ·
                refine ⟨1227637155890178054871517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3273699082373808146324045 1227637155890178054871517)
                ·
                  refine ⟨460363933458816770576819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1227637155890178054871517 460363933458816770576819)
                  ·
                    rfl

theorem cell21_2017250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 1, 3, 3].length) (baseStart_2017250 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2017250 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2017250 prefixEnd_2017250 := by exact prefixLift 2017250
  have htrace : WordTrace (prefixWord ++ tailWord_2017250) baseStart_2017250 baseEnd_2017250 := by
    simpa [prefixWord, tailWord_2017250, baseEnd_2017250] using wordTrace_append hprefix tailTrace_2017250
  have hstable : (prefixWord ++ tailWord_2017250).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2017250).length < 2 ^ (prefixWord ++ tailWord_2017250).sum := by decide
  have hdescent : baseEnd_2017250 < baseStart_2017250 := by decide
  rcases family_descends (prefixWord ++ tailWord_2017250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2017261 : List Nat := [1, 5, 1, 4, 2, 1, 7]
def baseStart_2017261 : Nat := 118140960795 + 2017261 * 2 ^ 59
def prefixEnd_2017261 : Nat := 4983230072969 + 3 ^ 40 * 2017261 * 2
def baseEnd_2017261 : Nat := 51151827089853688432607

theorem tailTrace_2017261 : CollatzResearch.WordTrace tailWord_2017261 prefixEnd_2017261 51151827089853688432607 := by
  unfold tailWord_2017261
  simp only [CollatzResearch.WordTrace]
  refine ⟨73575553144815392595211637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49050368763210261730141091 73575553144815392595211637)
  ·
    refine ⟨6897708107326443055801091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 73575553144815392595211637 6897708107326443055801091)
    ·
      refine ⟨10346562160989664583701637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6897708107326443055801091 10346562160989664583701637)
      ·
        refine ⟨1939980405185562109444057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10346562160989664583701637 1939980405185562109444057)
        ·
          refine ⟨1454985303889171582083043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1939980405185562109444057 1454985303889171582083043)
          ·
            refine ⟨2182477955833757373124565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1454985303889171582083043 2182477955833757373124565)
            ·
              refine ⟨51151827089853688432607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2182477955833757373124565 51151827089853688432607)
              ·
                rfl

theorem cell21_2017261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 7].length) (baseStart_2017261 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2017261 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2017261 prefixEnd_2017261 := by exact prefixLift 2017261
  have htrace : WordTrace (prefixWord ++ tailWord_2017261) baseStart_2017261 baseEnd_2017261 := by
    simpa [prefixWord, tailWord_2017261, baseEnd_2017261] using wordTrace_append hprefix tailTrace_2017261
  have hstable : (prefixWord ++ tailWord_2017261).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2017261).length < 2 ^ (prefixWord ++ tailWord_2017261).sum := by decide
  have hdescent : baseEnd_2017261 < baseStart_2017261 := by decide
  rcases family_descends (prefixWord ++ tailWord_2017261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2017320 : List Nat := [2, 1, 5, 3, 2, 8]
def baseStart_2017320 : Nat := 118140960795 + 2017320 * 2 ^ 59
def prefixEnd_2017320 : Nat := 4983230072969 + 3 ^ 40 * 2017320 * 2
def baseEnd_2017320 : Nat := 17051107718981933496667

theorem tailTrace_2017320 : CollatzResearch.WordTrace tailWord_2017320 prefixEnd_2017320 17051107718981933496667 := by
  unfold tailWord_2017320
  simp only [CollatzResearch.WordTrace]
  refine ⟨36788852525800822835804707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49051803367734430447739609 36788852525800822835804707)
  ·
    refine ⟨55183278788701234253707061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36788852525800822835804707 55183278788701234253707061)
    ·
      refine ⟨5173432386440740711285037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 55183278788701234253707061 5173432386440740711285037)
      ·
        refine ⟨1940037144915277766731889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5173432386440740711285037 1940037144915277766731889)
        ·
          refine ⟨1455027858686458325048917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1940037144915277766731889 1455027858686458325048917)
          ·
            refine ⟨17051107718981933496667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1455027858686458325048917 17051107718981933496667)
            ·
              rfl

theorem cell21_2017320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 8].length) (baseStart_2017320 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2017320 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2017320 prefixEnd_2017320 := by exact prefixLift 2017320
  have htrace : WordTrace (prefixWord ++ tailWord_2017320) baseStart_2017320 baseEnd_2017320 := by
    simpa [prefixWord, tailWord_2017320, baseEnd_2017320] using wordTrace_append hprefix tailTrace_2017320
  have hstable : (prefixWord ++ tailWord_2017320).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2017320).length < 2 ^ (prefixWord ++ tailWord_2017320).sum := by decide
  have hdescent : baseEnd_2017320 < baseStart_2017320 := by decide
  rcases family_descends (prefixWord ++ tailWord_2017320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2017331 : List Nat := [1, 1, 1, 2, 4, 1, 2, 3, 6]
def baseStart_2017331 : Nat := 118140960795 + 2017331 * 2 ^ 59
def prefixEnd_2017331 : Nat := 4983230072969 + 3 ^ 40 * 2017331 * 2
def baseEnd_2017331 : Nat := 460382418762378629726653

theorem tailTrace_2017331 : CollatzResearch.WordTrace tailWord_2017331 prefixEnd_2017331 460382418762378629726653 := by
  unfold tailWord_2017331
  simp only [CollatzResearch.WordTrace]
  refine ⟨73578106254561794550259847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49052070836374529700173231 73578106254561794550259847)
  ·
    refine ⟨110367159381842691825389771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73578106254561794550259847 110367159381842691825389771)
    ·
      refine ⟨165550739072764037738084657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110367159381842691825389771 165550739072764037738084657)
      ·
        refine ⟨124163054304573028303563493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165550739072764037738084657 124163054304573028303563493)
        ·
          refine ⟨23280572682107442806918155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 124163054304573028303563493 23280572682107442806918155)
          ·
            refine ⟨34920859023161164210377233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23280572682107442806918155 34920859023161164210377233)
            ·
              refine ⟨26190644267370873157782925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34920859023161164210377233 26190644267370873157782925)
              ·
                refine ⟨9821491600264077434168597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26190644267370873157782925 9821491600264077434168597)
                ·
                  refine ⟨460382418762378629726653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9821491600264077434168597 460382418762378629726653)
                  ·
                    rfl

theorem cell21_2017331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 3, 6].length) (baseStart_2017331 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2017331 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2017331 prefixEnd_2017331 := by exact prefixLift 2017331
  have htrace : WordTrace (prefixWord ++ tailWord_2017331) baseStart_2017331 baseEnd_2017331 := by
    simpa [prefixWord, tailWord_2017331, baseEnd_2017331] using wordTrace_append hprefix tailTrace_2017331
  have hstable : (prefixWord ++ tailWord_2017331).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2017331).length < 2 ^ (prefixWord ++ tailWord_2017331).sum := by decide
  have hdescent : baseEnd_2017331 < baseStart_2017331 := by decide
  rcases family_descends (prefixWord ++ tailWord_2017331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2017334 : List Nat := [5, 1, 2, 1, 1, 1, 2, 3, 5]
def baseStart_2017334 : Nat := 118140960795 + 2017334 * 2 ^ 59
def prefixEnd_2017334 : Nat := 4983230072969 + 3 ^ 40 * 2017334 * 2
def baseEnd_2017334 : Nat := 460383103403251291176647

theorem tailTrace_2017334 : CollatzResearch.WordTrace tailWord_2017334 prefixEnd_2017334 460383103403251291176647 := by
  unfold tailWord_2017334
  simp only [CollatzResearch.WordTrace]
  refine ⟨4598638479596932878913691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 49052143782367284041746037 4598638479596932878913691)
  ·
    refine ⟨6897957719395399318370537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4598638479596932878913691 6897957719395399318370537)
    ·
      refine ⟨5173468289546549488777903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6897957719395399318370537 5173468289546549488777903)
      ·
        refine ⟨7760202434319824233166855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5173468289546549488777903 7760202434319824233166855)
        ·
          refine ⟨11640303651479736349750283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7760202434319824233166855 11640303651479736349750283)
          ·
            refine ⟨17460455477219604524625425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11640303651479736349750283 17460455477219604524625425)
            ·
              refine ⟨13095341607914703393469069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17460455477219604524625425 13095341607914703393469069)
              ·
                refine ⟨4910753102968013772550901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13095341607914703393469069 4910753102968013772550901)
                ·
                  refine ⟨460383103403251291176647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4910753102968013772550901 460383103403251291176647)
                  ·
                    rfl

theorem cell21_2017334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 3, 5].length) (baseStart_2017334 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2017334 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2017334 prefixEnd_2017334 := by exact prefixLift 2017334
  have htrace : WordTrace (prefixWord ++ tailWord_2017334) baseStart_2017334 baseEnd_2017334 := by
    simpa [prefixWord, tailWord_2017334, baseEnd_2017334] using wordTrace_append hprefix tailTrace_2017334
  have hstable : (prefixWord ++ tailWord_2017334).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2017334).length < 2 ^ (prefixWord ++ tailWord_2017334).sum := by decide
  have hdescent : baseEnd_2017334 < baseStart_2017334 := by decide
  rcases family_descends (prefixWord ++ tailWord_2017334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2017393 : List Nat := [1, 2, 2, 2, 1, 1, 6, 1, 5]
def baseStart_2017393 : Nat := 118140960795 + 2017393 * 2 ^ 59
def prefixEnd_2017393 : Nat := 4983230072969 + 3 ^ 40 * 2017393 * 2
def baseEnd_2017393 : Nat := 460396568007080299693193

theorem tailTrace_2017393 : CollatzResearch.WordTrace tailWord_2017393 prefixEnd_2017393 460396568007080299693193 := by
  unfold tailWord_2017393
  simp only [CollatzResearch.WordTrace]
  refine ⟨73580367580337179139016833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49053578386891452759344555 73580367580337179139016833)
  ·
    refine ⟨55185275685252884354262625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73580367580337179139016833 55185275685252884354262625)
    ·
      refine ⟨41388956763939663265696969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55185275685252884354262625 41388956763939663265696969)
      ·
        refine ⟨31041717572954747449272727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41388956763939663265696969 31041717572954747449272727)
        ·
          refine ⟨46562576359432121173909091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31041717572954747449272727 46562576359432121173909091)
          ·
            refine ⟨69843864539148181760863637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46562576359432121173909091 69843864539148181760863637)
            ·
              refine ⟨3273931150272571020040483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 69843864539148181760863637 3273931150272571020040483)
              ·
                refine ⟨4910896725408856530060725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3273931150272571020040483 4910896725408856530060725)
                ·
                  refine ⟨460396568007080299693193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4910896725408856530060725 460396568007080299693193)
                  ·
                    rfl

theorem cell21_2017393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 6, 1, 5].length) (baseStart_2017393 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2017393 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2017393 prefixEnd_2017393 := by exact prefixLift 2017393
  have htrace : WordTrace (prefixWord ++ tailWord_2017393) baseStart_2017393 baseEnd_2017393 := by
    simpa [prefixWord, tailWord_2017393, baseEnd_2017393] using wordTrace_append hprefix tailTrace_2017393
  have hstable : (prefixWord ++ tailWord_2017393).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2017393).length < 2 ^ (prefixWord ++ tailWord_2017393).sum := by decide
  have hdescent : baseEnd_2017393 < baseStart_2017393 := by decide
  rcases family_descends (prefixWord ++ tailWord_2017393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2017444 : List Nat := [2, 3, 1, 2, 4, 1, 3, 2, 3]
def baseStart_2017444 : Nat := 118140960795 + 2017444 * 2 ^ 59
def prefixEnd_2017444 : Nat := 4983230072969 + 3 ^ 40 * 2017444 * 2
def baseEnd_2017444 : Nat := 460408206901915544343089

theorem tailTrace_2017444 : CollatzResearch.WordTrace tailWord_2017444 prefixEnd_2017444 460408206901915544343089 := by
  unfold tailWord_2017444
  simp only [CollatzResearch.WordTrace]
  refine ⟨36791113851576207424561693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49054818468768276566082257 36791113851576207424561693)
  ·
    refine ⟨13796667694341077784210635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36791113851576207424561693 13796667694341077784210635)
    ·
      refine ⟨20695001541511616676315953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13796667694341077784210635 20695001541511616676315953)
      ·
        refine ⟨15521251156133712507236965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20695001541511616676315953 15521251156133712507236965)
        ·
          refine ⟨2910234591775071095106931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15521251156133712507236965 2910234591775071095106931)
          ·
            refine ⟨4365351887662606642660397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2910234591775071095106931 4365351887662606642660397)
            ·
              refine ⟨1637006957873477490997649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4365351887662606642660397 1637006957873477490997649)
              ·
                refine ⟨1227755218405108118248237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1637006957873477490997649 1227755218405108118248237)
                ·
                  refine ⟨460408206901915544343089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1227755218405108118248237 460408206901915544343089)
                  ·
                    rfl

theorem cell21_2017444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 3, 2, 3].length) (baseStart_2017444 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2017444 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2017444 prefixEnd_2017444 := by exact prefixLift 2017444
  have htrace : WordTrace (prefixWord ++ tailWord_2017444) baseStart_2017444 baseEnd_2017444 := by
    simpa [prefixWord, tailWord_2017444, baseEnd_2017444] using wordTrace_append hprefix tailTrace_2017444
  have hstable : (prefixWord ++ tailWord_2017444).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2017444).length < 2 ^ (prefixWord ++ tailWord_2017444).sum := by decide
  have hdescent : baseEnd_2017444 < baseStart_2017444 := by decide
  rcases family_descends (prefixWord ++ tailWord_2017444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2017506 : List Nat := [3, 3, 4, 1, 1, 2, 1, 6]
def baseStart_2017506 : Nat := 118140960795 + 2017506 * 2 ^ 59
def prefixEnd_2017506 : Nat := 4983230072969 + 3 ^ 40 * 2017506 * 2
def baseEnd_2017506 : Nat := 153474118715539071436543

theorem tailTrace_2017506 : CollatzResearch.WordTrace tailWord_2017506 prefixEnd_2017506 153474118715539071436543 := by
  unfold tailWord_2017506
  simp only [CollatzResearch.WordTrace]
  refine ⟨18396122257231949859470093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49056326019285199625253581 18396122257231949859470093)
  ·
    refine ⟨6898545846461981197301285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18396122257231949859470093 6898545846461981197301285)
    ·
      refine ⟨1293477346211621474493991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6898545846461981197301285 1293477346211621474493991)
      ·
        refine ⟨1940216019317432211740987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1293477346211621474493991 1940216019317432211740987)
        ·
          refine ⟨2910324028976148317611481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1940216019317432211740987 2910324028976148317611481)
          ·
            refine ⟨2182743021732111238208611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2910324028976148317611481 2182743021732111238208611)
            ·
              refine ⟨3274114532598166857312917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2182743021732111238208611 3274114532598166857312917)
              ·
                refine ⟨153474118715539071436543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3274114532598166857312917 153474118715539071436543)
                ·
                  rfl

theorem cell21_2017506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 1, 6].length) (baseStart_2017506 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2017506 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2017506 prefixEnd_2017506 := by exact prefixLift 2017506
  have htrace : WordTrace (prefixWord ++ tailWord_2017506) baseStart_2017506 baseEnd_2017506 := by
    simpa [prefixWord, tailWord_2017506, baseEnd_2017506] using wordTrace_append hprefix tailTrace_2017506
  have hstable : (prefixWord ++ tailWord_2017506).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2017506).length < 2 ^ (prefixWord ++ tailWord_2017506).sum := by decide
  have hdescent : baseEnd_2017506 < baseStart_2017506 := by decide
  rcases family_descends (prefixWord ++ tailWord_2017506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2017562 : List Nat := [3, 1, 1, 3, 4, 1, 2, 1, 5]
def baseStart_2017562 : Nat := 118140960795 + 2017562 * 2 ^ 59
def prefixEnd_2017562 : Nat := 4983230072969 + 3 ^ 40 * 2017562 * 2
def baseEnd_2017562 : Nat := 460435136109573561376181

theorem tailTrace_2017562 : CollatzResearch.WordTrace tailWord_2017562 prefixEnd_2017562 460435136109573561376181 := by
  unfold tailWord_2017562
  simp only [CollatzResearch.WordTrace]
  refine ⟨18396632879181230250479735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49057687677816614001279293 18396632879181230250479735)
  ·
    refine ⟨27594949318771845375719603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18396632879181230250479735 27594949318771845375719603)
    ·
      refine ⟨41392423978157768063579405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27594949318771845375719603 41392423978157768063579405)
      ·
        refine ⟨15522158991809163023842277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41392423978157768063579405 15522158991809163023842277)
        ·
          refine ⟨2910404810964218066970427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15522158991809163023842277 2910404810964218066970427)
          ·
            refine ⟨4365607216446327100455641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2910404810964218066970427 4365607216446327100455641)
            ·
              refine ⟨3274205412334745325341731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4365607216446327100455641 3274205412334745325341731)
              ·
                refine ⟨4911308118502117988012597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3274205412334745325341731 4911308118502117988012597)
                ·
                  refine ⟨460435136109573561376181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4911308118502117988012597 460435136109573561376181)
                  ·
                    rfl

theorem cell21_2017562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 2, 1, 5].length) (baseStart_2017562 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2017562 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2017562 prefixEnd_2017562 := by exact prefixLift 2017562
  have htrace : WordTrace (prefixWord ++ tailWord_2017562) baseStart_2017562 baseEnd_2017562 := by
    simpa [prefixWord, tailWord_2017562, baseEnd_2017562] using wordTrace_append hprefix tailTrace_2017562
  have hstable : (prefixWord ++ tailWord_2017562).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2017562).length < 2 ^ (prefixWord ++ tailWord_2017562).sum := by decide
  have hdescent : baseEnd_2017562 < baseStart_2017562 := by decide
  rcases family_descends (prefixWord ++ tailWord_2017562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2017582 : List Nat := [4, 1, 3, 3, 2, 1, 2, 5]
def baseStart_2017582 : Nat := 118140960795 + 2017582 * 2 ^ 59
def prefixEnd_2017582 : Nat := 4983230072969 + 3 ^ 40 * 2017582 * 2
def baseEnd_2017582 : Nat := 153479900127352657014269

theorem tailTrace_2017582 : CollatzResearch.WordTrace tailWord_2017582 prefixEnd_2017582 153479900127352657014269 := by
  unfold tailWord_2017582
  simp only [CollatzResearch.WordTrace]
  refine ⟨9198407622081558052205875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49058173984434976278431333 9198407622081558052205875)
  ·
    refine ⟨13797611433122337078308813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9198407622081558052205875 13797611433122337078308813)
    ·
      refine ⟨5174104287420876404365805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13797611433122337078308813 5174104287420876404365805)
      ·
        refine ⟨1940289107782828651637177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5174104287420876404365805 1940289107782828651637177)
        ·
          refine ⟨1455216830837121488727883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1940289107782828651637177 1455216830837121488727883)
          ·
            refine ⟨2182825246255682233091825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1455216830837121488727883 2182825246255682233091825)
            ·
              refine ⟨1637118934691761674818869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2182825246255682233091825 1637118934691761674818869)
              ·
                refine ⟨153479900127352657014269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1637118934691761674818869 153479900127352657014269)
                ·
                  rfl

theorem cell21_2017582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 2, 5].length) (baseStart_2017582 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2017582 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2017582 prefixEnd_2017582 := by exact prefixLift 2017582
  have htrace : WordTrace (prefixWord ++ tailWord_2017582) baseStart_2017582 baseEnd_2017582 := by
    simpa [prefixWord, tailWord_2017582, baseEnd_2017582] using wordTrace_append hprefix tailTrace_2017582
  have hstable : (prefixWord ++ tailWord_2017582).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2017582).length < 2 ^ (prefixWord ++ tailWord_2017582).sum := by decide
  have hdescent : baseEnd_2017582 < baseStart_2017582 := by decide
  rcases family_descends (prefixWord ++ tailWord_2017582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2017714 : List Nat := [3, 2, 1, 1, 1, 1, 6, 3, 3]
def baseStart_2017714 : Nat := 118140960795 + 2017714 * 2 ^ 59
def prefixEnd_2017714 : Nat := 4983230072969 + 3 ^ 40 * 2017714 * 2
def baseEnd_2017714 : Nat := 460469824580455074842537

theorem tailTrace_2017714 : CollatzResearch.WordTrace tailWord_2017714 prefixEnd_2017714 460469824580455074842537 := by
  unfold tailWord_2017714
  simp only [CollatzResearch.WordTrace]
  refine ⟨18398018853043562740363049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49061383608116167307634797 18398018853043562740363049)
  ·
    refine ⟨13798514139782672055272287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18398018853043562740363049 13798514139782672055272287)
    ·
      refine ⟨20697771209674008082908431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13798514139782672055272287 20697771209674008082908431)
      ·
        refine ⟨31046656814511012124362647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20697771209674008082908431 31046656814511012124362647)
        ·
          refine ⟨46569985221766518186543971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31046656814511012124362647 46569985221766518186543971)
          ·
            refine ⟨69854977832649777279815957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46569985221766518186543971 69854977832649777279815957)
            ·
              refine ⟨3274452085905458309991373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 69854977832649777279815957 3274452085905458309991373)
              ·
                refine ⟨1227919532214546866246765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3274452085905458309991373 1227919532214546866246765)
                ·
                  refine ⟨460469824580455074842537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1227919532214546866246765 460469824580455074842537)
                  ·
                    rfl

theorem cell21_2017714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 6, 3, 3].length) (baseStart_2017714 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2017714 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2017714 prefixEnd_2017714 := by exact prefixLift 2017714
  have htrace : WordTrace (prefixWord ++ tailWord_2017714) baseStart_2017714 baseEnd_2017714 := by
    simpa [prefixWord, tailWord_2017714, baseEnd_2017714] using wordTrace_append hprefix tailTrace_2017714
  have hstable : (prefixWord ++ tailWord_2017714).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2017714).length < 2 ^ (prefixWord ++ tailWord_2017714).sum := by decide
  have hdescent : baseEnd_2017714 < baseStart_2017714 := by decide
  rcases family_descends (prefixWord ++ tailWord_2017714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2017759 : List Nat := [1, 1, 2, 3, 3, 4, 2, 5]
def baseStart_2017759 : Nat := 118140960795 + 2017759 * 2 ^ 59
def prefixEnd_2017759 : Nat := 4983230072969 + 3 ^ 40 * 2017759 * 2
def baseEnd_2017759 : Nat := 153493364731181665530815

theorem tailTrace_2017759 : CollatzResearch.WordTrace tailWord_2017759 prefixEnd_2017759 153493364731181665530815 := by
  unfold tailWord_2017759
  simp only [CollatzResearch.WordTrace]
  refine ⟨73593716697011223646840331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49062477798007482431226887 73593716697011223646840331)
  ·
    refine ⟨110390575045516835470260497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73593716697011223646840331 110390575045516835470260497)
    ·
      refine ⟨82792931284137626602695373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110390575045516835470260497 82792931284137626602695373)
      ·
        refine ⟨31047349231551609976010765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82792931284137626602695373 31047349231551609976010765)
        ·
          refine ⟨11642755961831853741004037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31047349231551609976010765 11642755961831853741004037)
          ·
            refine ⟨2183016742843472576438257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11642755961831853741004037 2183016742843472576438257)
            ·
              refine ⟨1637262557132604432328693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2183016742843472576438257 1637262557132604432328693)
              ·
                refine ⟨153493364731181665530815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1637262557132604432328693 153493364731181665530815)
                ·
                  rfl

theorem cell21_2017759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 2, 5].length) (baseStart_2017759 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2017759 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2017759 prefixEnd_2017759 := by exact prefixLift 2017759
  have htrace : WordTrace (prefixWord ++ tailWord_2017759) baseStart_2017759 baseEnd_2017759 := by
    simpa [prefixWord, tailWord_2017759, baseEnd_2017759] using wordTrace_append hprefix tailTrace_2017759
  have hstable : (prefixWord ++ tailWord_2017759).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2017759).length < 2 ^ (prefixWord ++ tailWord_2017759).sum := by decide
  have hdescent : baseEnd_2017759 < baseStart_2017759 := by decide
  rcases family_descends (prefixWord ++ tailWord_2017759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2017804 : List Nat := [2, 2, 1, 2, 4, 2, 1, 3, 4]
def baseStart_2017804 : Nat := 118140960795 + 2017804 * 2 ^ 59
def prefixEnd_2017804 : Nat := 4983230072969 + 3 ^ 40 * 2017804 * 2
def baseEnd_2017804 : Nat := 460490363806634918342353

theorem tailTrace_2017804 : CollatzResearch.WordTrace tailWord_2017804 prefixEnd_2017804 460490363806634918342353 := by
  unfold tailWord_2017804
  simp only [CollatzResearch.WordTrace]
  refine ⟨36797678990924098166114233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49063571987898797554818977 36797678990924098166114233)
  ·
    refine ⟨27598259243193073624585675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36797678990924098166114233 27598259243193073624585675)
    ·
      refine ⟨41397388864789610436878513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27598259243193073624585675 41397388864789610436878513)
      ·
        refine ⟨31048041648592207827658885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41397388864789610436878513 31048041648592207827658885)
        ·
          refine ⟨5821507809111038967686041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31048041648592207827658885 5821507809111038967686041)
          ·
            refine ⟨4366130856833279225764531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5821507809111038967686041 4366130856833279225764531)
            ·
              refine ⟨6549196285249918838646797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4366130856833279225764531 6549196285249918838646797)
              ·
                refine ⟨2455948606968719564492549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6549196285249918838646797 2455948606968719564492549)
                ·
                  refine ⟨460490363806634918342353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2455948606968719564492549 460490363806634918342353)
                  ·
                    rfl

theorem cell21_2017804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 1, 3, 4].length) (baseStart_2017804 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2017804 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2017804 prefixEnd_2017804 := by exact prefixLift 2017804
  have htrace : WordTrace (prefixWord ++ tailWord_2017804) baseStart_2017804 baseEnd_2017804 := by
    simpa [prefixWord, tailWord_2017804, baseEnd_2017804] using wordTrace_append hprefix tailTrace_2017804
  have hstable : (prefixWord ++ tailWord_2017804).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2017804).length < 2 ^ (prefixWord ++ tailWord_2017804).sum := by decide
  have hdescent : baseEnd_2017804 < baseStart_2017804 := by decide
  rcases family_descends (prefixWord ++ tailWord_2017804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2017877 : List Nat := [1, 3, 2, 2, 1, 1, 2, 9]
def baseStart_2017877 : Nat := 118140960795 + 2017877 * 2 ^ 59
def prefixEnd_2017877 : Nat := 4983230072969 + 3 ^ 40 * 2017877 * 2
def baseEnd_2017877 : Nat := 153502341133734337875179

theorem tailTrace_2017877 : CollatzResearch.WordTrace tailWord_2017877 prefixEnd_2017877 153502341133734337875179 := by
  unfold tailWord_2017877
  simp only [CollatzResearch.WordTrace]
  refine ⟨73598020510583729799635885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49065347007055819866423923 73598020510583729799635885)
  ·
    refine ⟨27599257691468898674863457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73598020510583729799635885 27599257691468898674863457)
    ·
      refine ⟨20699443268601674006147593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27599257691468898674863457 20699443268601674006147593)
      ·
        refine ⟨15524582451451255504610695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20699443268601674006147593 15524582451451255504610695)
        ·
          refine ⟨23286873677176883256916043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15524582451451255504610695 23286873677176883256916043)
          ·
            refine ⟨34930310515765324885374065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23286873677176883256916043 34930310515765324885374065)
            ·
              refine ⟨26197732886823993664030549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34930310515765324885374065 26197732886823993664030549)
              ·
                refine ⟨153502341133734337875179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 26197732886823993664030549 153502341133734337875179)
                ·
                  rfl

theorem cell21_2017877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 9].length) (baseStart_2017877 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2017877 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2017877 prefixEnd_2017877 := by exact prefixLift 2017877
  have htrace : WordTrace (prefixWord ++ tailWord_2017877) baseStart_2017877 baseEnd_2017877 := by
    simpa [prefixWord, tailWord_2017877, baseEnd_2017877] using wordTrace_append hprefix tailTrace_2017877
  have hstable : (prefixWord ++ tailWord_2017877).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2017877).length < 2 ^ (prefixWord ++ tailWord_2017877).sum := by decide
  have hdescent : baseEnd_2017877 < baseStart_2017877 := by decide
  rcases family_descends (prefixWord ++ tailWord_2017877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2017959 : List Nat := [1, 1, 6, 3, 1, 2, 1, 1, 5]
def baseStart_2017959 : Nat := 118140960795 + 2017959 * 2 ^ 59
def prefixEnd_2017959 : Nat := 4983230072969 + 3 ^ 40 * 2017959 * 2
def baseEnd_2017959 : Nat := 460525736918389093258703

theorem tailTrace_2017959 : CollatzResearch.WordTrace tailWord_2017959 prefixEnd_2017959 460525736918389093258703 := by
  unfold tailWord_2017959
  simp only [CollatzResearch.WordTrace]
  refine ⟨73601011296286657804120931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49067340864191105202747287 73601011296286657804120931)
  ·
    refine ⟨110401516944429986706181397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73601011296286657804120931 110401516944429986706181397)
    ·
      refine ⟨5175071106770155626852253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 110401516944429986706181397 5175071106770155626852253)
      ·
        refine ⟨1940651665038808360069595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5175071106770155626852253 1940651665038808360069595)
        ·
          refine ⟨2910977497558212540104393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1940651665038808360069595 2910977497558212540104393)
          ·
            refine ⟨2183233123168659405078295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2910977497558212540104393 2183233123168659405078295)
            ·
              refine ⟨3274849684752989107617443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2183233123168659405078295 3274849684752989107617443)
              ·
                refine ⟨4912274527129483661426165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3274849684752989107617443 4912274527129483661426165)
                ·
                  refine ⟨460525736918389093258703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4912274527129483661426165 460525736918389093258703)
                  ·
                    rfl

theorem cell21_2017959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 1, 1, 5].length) (baseStart_2017959 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2017959 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2017959 prefixEnd_2017959 := by exact prefixLift 2017959
  have htrace : WordTrace (prefixWord ++ tailWord_2017959) baseStart_2017959 baseEnd_2017959 := by
    simpa [prefixWord, tailWord_2017959, baseEnd_2017959] using wordTrace_append hprefix tailTrace_2017959
  have hstable : (prefixWord ++ tailWord_2017959).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2017959).length < 2 ^ (prefixWord ++ tailWord_2017959).sum := by decide
  have hdescent : baseEnd_2017959 < baseStart_2017959 := by decide
  rcases family_descends (prefixWord ++ tailWord_2017959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2017973 : List Nat := [1, 3, 3, 3, 1, 1, 4, 1, 4]
def baseStart_2017973 : Nat := 118140960795 + 2017973 * 2 ^ 59
def prefixEnd_2017973 : Nat := 4983230072969 + 3 ^ 40 * 2017973 * 2
def baseEnd_2017973 : Nat := 460528931909128180025341

theorem tailTrace_2017973 : CollatzResearch.WordTrace tailWord_2017973 prefixEnd_2017973 460528931909128180025341 := by
  unfold tailWord_2017973
  simp only [CollatzResearch.WordTrace]
  refine ⟨73601521918235938195130573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49067681278823958796753715 73601521918235938195130573)
  ·
    refine ⟨27600570719338476823173965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73601521918235938195130573 27600570719338476823173965)
    ·
      refine ⟨10350214019751928808690237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27600570719338476823173965 10350214019751928808690237)
      ·
        refine ⟨3881330257406973303258839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10350214019751928808690237 3881330257406973303258839)
        ·
          refine ⟨5821995386110459954888259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3881330257406973303258839 5821995386110459954888259)
          ·
            refine ⟨8732993079165689932332389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5821995386110459954888259 8732993079165689932332389)
            ·
              refine ⟨1637436202343566862312323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8732993079165689932332389 1637436202343566862312323)
              ·
                refine ⟨2456154303515350293468485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1637436202343566862312323 2456154303515350293468485)
                ·
                  refine ⟨460528931909128180025341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2456154303515350293468485 460528931909128180025341)
                  ·
                    rfl

theorem cell21_2017973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 4, 1, 4].length) (baseStart_2017973 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2017973 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2017973 prefixEnd_2017973 := by exact prefixLift 2017973
  have htrace : WordTrace (prefixWord ++ tailWord_2017973) baseStart_2017973 baseEnd_2017973 := by
    simpa [prefixWord, tailWord_2017973, baseEnd_2017973] using wordTrace_append hprefix tailTrace_2017973
  have hstable : (prefixWord ++ tailWord_2017973).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2017973).length < 2 ^ (prefixWord ++ tailWord_2017973).sum := by decide
  have hdescent : baseEnd_2017973 < baseStart_2017973 := by decide
  rcases family_descends (prefixWord ++ tailWord_2017973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2018001 : List Nat := [1, 2, 2, 1, 2, 3, 2, 5, 3]
def baseStart_2018001 : Nat := 118140960795 + 2018001 * 2 ^ 59
def prefixEnd_2018001 : Nat := 4983230072969 + 3 ^ 40 * 2018001 * 2
def baseEnd_2018001 : Nat := 460535321890606353558617

theorem tailTrace_2018001 : CollatzResearch.WordTrace tailWord_2018001 prefixEnd_2018001 460535321890606353558617 := by
  unfold tailWord_2018001
  simp only [CollatzResearch.WordTrace]
  refine ⟨73602543162134498977149857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49068362108089665984766571 73602543162134498977149857)
  ·
    refine ⟨55201907371600874232862393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73602543162134498977149857 55201907371600874232862393)
    ·
      refine ⟨41401430528700655674646795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55201907371600874232862393 41401430528700655674646795)
      ·
        refine ⟨62102145793050983511970193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41401430528700655674646795 62102145793050983511970193)
        ·
          refine ⟨46576609344788237633977645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62102145793050983511970193 46576609344788237633977645)
          ·
            refine ⟨17466228504295589112741617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46576609344788237633977645 17466228504295589112741617)
            ·
              refine ⟨13099671378221691834556213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17466228504295589112741617 13099671378221691834556213)
              ·
                refine ⟨1228094191708283609489645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13099671378221691834556213 1228094191708283609489645)
                ·
                  refine ⟨460535321890606353558617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1228094191708283609489645 460535321890606353558617)
                  ·
                    rfl

theorem cell21_2018001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 5, 3].length) (baseStart_2018001 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2018001 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2018001 prefixEnd_2018001 := by exact prefixLift 2018001
  have htrace : WordTrace (prefixWord ++ tailWord_2018001) baseStart_2018001 baseEnd_2018001 := by
    simpa [prefixWord, tailWord_2018001, baseEnd_2018001] using wordTrace_append hprefix tailTrace_2018001
  have hstable : (prefixWord ++ tailWord_2018001).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2018001).length < 2 ^ (prefixWord ++ tailWord_2018001).sum := by decide
  have hdescent : baseEnd_2018001 < baseStart_2018001 := by decide
  rcases family_descends (prefixWord ++ tailWord_2018001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2018015 : List Nat := [1, 1, 2, 3, 2, 3, 1, 4, 4]
def baseStart_2018015 : Nat := 118140960795 + 2018015 * 2 ^ 59
def prefixEnd_2018015 : Nat := 4983230072969 + 3 ^ 40 * 2018015 * 2
def baseEnd_2018015 : Nat := 460538516881345440325255

theorem tailTrace_2018015 : CollatzResearch.WordTrace tailWord_2018015 prefixEnd_2018015 460538516881345440325255 := by
  unfold tailWord_2018015
  simp only [CollatzResearch.WordTrace]
  refine ⟨73603053784083779368159499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49068702522722519578772999 73603053784083779368159499)
  ·
    refine ⟨110404580676125669052239249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73603053784083779368159499 110404580676125669052239249)
    ·
      refine ⟨82803435507094251789179437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110404580676125669052239249 82803435507094251789179437)
      ·
        refine ⟨31051288315160344420942289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82803435507094251789179437 31051288315160344420942289)
        ·
          refine ⟨23288466236370258315706717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31051288315160344420942289 23288466236370258315706717)
          ·
            refine ⟨8733174838638846868390019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23288466236370258315706717 8733174838638846868390019)
            ·
              refine ⟨13099762257958270302585029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8733174838638846868390019 13099762257958270302585029)
              ·
                refine ⟨2456205423367175681734693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13099762257958270302585029 2456205423367175681734693)
                ·
                  refine ⟨460538516881345440325255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2456205423367175681734693 460538516881345440325255)
                  ·
                    rfl

theorem cell21_2018015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 4, 4].length) (baseStart_2018015 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2018015 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2018015 prefixEnd_2018015 := by exact prefixLift 2018015
  have htrace : WordTrace (prefixWord ++ tailWord_2018015) baseStart_2018015 baseEnd_2018015 := by
    simpa [prefixWord, tailWord_2018015, baseEnd_2018015] using wordTrace_append hprefix tailTrace_2018015
  have hstable : (prefixWord ++ tailWord_2018015).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2018015).length < 2 ^ (prefixWord ++ tailWord_2018015).sum := by decide
  have hdescent : baseEnd_2018015 < baseStart_2018015 := by decide
  rcases family_descends (prefixWord ++ tailWord_2018015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2018066 : List Nat := [3, 2, 4, 1, 2, 2, 1, 2, 4]
def baseStart_2018066 : Nat := 118140960795 + 2018066 * 2 ^ 59
def prefixEnd_2018066 : Nat := 4983230072969 + 3 ^ 40 * 2018066 * 2
def baseEnd_2018066 : Nat := 460550155776180684975151

theorem tailTrace_2018066 : CollatzResearch.WordTrace tailWord_2018066 prefixEnd_2018066 460550155776180684975151 := by
  unfold tailWord_2018066
  simp only [CollatzResearch.WordTrace]
  refine ⟨18401228476724753769566513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49069942604599343385510701 18401228476724753769566513)
  ·
    refine ⟨13800921357543565327174885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18401228476724753769566513 13800921357543565327174885)
    ·
      refine ⟨2587672754539418498845291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13800921357543565327174885 2587672754539418498845291)
      ·
        refine ⟨3881509131809127748267937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2587672754539418498845291 3881509131809127748267937)
        ·
          refine ⟨2911131848856845811200953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3881509131809127748267937 2911131848856845811200953)
          ·
            refine ⟨2183348886642634358400715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2911131848856845811200953 2183348886642634358400715)
            ·
              refine ⟨3275023329963951537601073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2183348886642634358400715 3275023329963951537601073)
              ·
                refine ⟨2456267497472963653200805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3275023329963951537601073 2456267497472963653200805)
                ·
                  refine ⟨460550155776180684975151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2456267497472963653200805 460550155776180684975151)
                  ·
                    rfl

theorem cell21_2018066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 1, 2, 4].length) (baseStart_2018066 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2018066 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2018066 prefixEnd_2018066 := by exact prefixLift 2018066
  have htrace : WordTrace (prefixWord ++ tailWord_2018066) baseStart_2018066 baseEnd_2018066 := by
    simpa [prefixWord, tailWord_2018066, baseEnd_2018066] using wordTrace_append hprefix tailTrace_2018066
  have hstable : (prefixWord ++ tailWord_2018066).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2018066).length < 2 ^ (prefixWord ++ tailWord_2018066).sum := by decide
  have hdescent : baseEnd_2018066 < baseStart_2018066 := by decide
  rcases family_descends (prefixWord ++ tailWord_2018066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2018184 : List Nat := [2, 1, 3, 3, 2, 2, 2, 2, 4]
def baseStart_2018184 : Nat := 118140960795 + 2018184 * 2 ^ 59
def prefixEnd_2018184 : Nat := 4983230072969 + 3 ^ 40 * 2018184 * 2
def baseEnd_2018184 : Nat := 460577084983838702008243

theorem tailTrace_2018184 : CollatzResearch.WordTrace tailWord_2018184 prefixEnd_2018184 460577084983838702008243 := by
  unfold tailWord_2018184
  simp only [CollatzResearch.WordTrace]
  refine ⟨36804608860235760615530803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49072811813647680820707737 36804608860235760615530803)
  ·
    refine ⟨55206913290353640923296205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36804608860235760615530803 55206913290353640923296205)
    ·
      refine ⟨20702592483882615346236077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55206913290353640923296205 20702592483882615346236077)
      ·
        refine ⟨7763472181455980754838529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20702592483882615346236077 7763472181455980754838529)
        ·
          refine ⟨5822604136091985566128897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7763472181455980754838529 5822604136091985566128897)
          ·
            refine ⟨4366953102068989174596673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5822604136091985566128897 4366953102068989174596673)
            ·
              refine ⟨3275214826551741880947505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4366953102068989174596673 3275214826551741880947505)
              ·
                refine ⟨2456411119913806410710629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3275214826551741880947505 2456411119913806410710629)
                ·
                  refine ⟨460577084983838702008243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2456411119913806410710629 460577084983838702008243)
                  ·
                    rfl

theorem cell21_2018184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 2, 2, 4].length) (baseStart_2018184 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2018184 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2018184 prefixEnd_2018184 := by exact prefixLift 2018184
  have htrace : WordTrace (prefixWord ++ tailWord_2018184) baseStart_2018184 baseEnd_2018184 := by
    simpa [prefixWord, tailWord_2018184, baseEnd_2018184] using wordTrace_append hprefix tailTrace_2018184
  have hstable : (prefixWord ++ tailWord_2018184).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2018184).length < 2 ^ (prefixWord ++ tailWord_2018184).sum := by decide
  have hdescent : baseEnd_2018184 < baseStart_2018184 := by decide
  rcases family_descends (prefixWord ++ tailWord_2018184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2018212 : List Nat := [2, 3, 1, 2, 1, 2, 3, 2, 5]
def baseStart_2018212 : Nat := 118140960795 + 2018212 * 2 ^ 59
def prefixEnd_2018212 : Nat := 4983230072969 + 3 ^ 40 * 2018212 * 2
def baseEnd_2018212 : Nat := 460583474965316875541519

theorem tailTrace_2018212 : CollatzResearch.WordTrace tailWord_2018212 prefixEnd_2018212 460583474965316875541519 := by
  unfold tailWord_2018212
  simp only [CollatzResearch.WordTrace]
  refine ⟨36805119482185041006540445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49073492642913388008720593 36805119482185041006540445)
  ·
    refine ⟨13801919805819390377452667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36805119482185041006540445 13801919805819390377452667)
    ·
      refine ⟨20702879708729085566179001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13801919805819390377452667 20702879708729085566179001)
      ·
        refine ⟨15527159781546814174634251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20702879708729085566179001 15527159781546814174634251)
        ·
          refine ⟨23290739672320221261951377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15527159781546814174634251 23290739672320221261951377)
          ·
            refine ⟨17468054754240165946463533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23290739672320221261951377 17468054754240165946463533)
            ·
              refine ⟨6550520532840062229923825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17468054754240165946463533 6550520532840062229923825)
              ·
                refine ⟨4912890399630046672442869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6550520532840062229923825 4912890399630046672442869)
                ·
                  refine ⟨460583474965316875541519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4912890399630046672442869 460583474965316875541519)
                  ·
                    rfl

theorem cell21_2018212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 3, 2, 5].length) (baseStart_2018212 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2018212 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2018212 prefixEnd_2018212 := by exact prefixLift 2018212
  have htrace : WordTrace (prefixWord ++ tailWord_2018212) baseStart_2018212 baseEnd_2018212 := by
    simpa [prefixWord, tailWord_2018212, baseEnd_2018212] using wordTrace_append hprefix tailTrace_2018212
  have hstable : (prefixWord ++ tailWord_2018212).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2018212).length < 2 ^ (prefixWord ++ tailWord_2018212).sum := by decide
  have hdescent : baseEnd_2018212 < baseStart_2018212 := by decide
  rcases family_descends (prefixWord ++ tailWord_2018212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2018215 : List Nat := [1, 1, 6, 1, 3, 1, 3, 5]
def baseStart_2018215 : Nat := 118140960795 + 2018215 * 2 ^ 59
def prefixEnd_2018215 : Nat := 4983230072969 + 3 ^ 40 * 2018215 * 2
def baseEnd_2018215 : Nat := 153528053202063178997171

theorem tailTrace_2018215 : CollatzResearch.WordTrace tailWord_2018215 prefixEnd_2018215 153528053202063178997171 := by
  unfold tailWord_2018215
  simp only [CollatzResearch.WordTrace]
  refine ⟨73610348383359213525440099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49073565588906142350293399 73610348383359213525440099)
  ·
    refine ⟨110415522575038820288160149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73610348383359213525440099 110415522575038820288160149)
    ·
      refine ⟨5175727620704944701007507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 110415522575038820288160149 5175727620704944701007507)
      ·
        refine ⟨7763591431057417051511261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5175727620704944701007507 7763591431057417051511261)
        ·
          refine ⟨2911346786646531394316723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7763591431057417051511261 2911346786646531394316723)
          ·
            refine ⟨4367020179969797091475085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2911346786646531394316723 4367020179969797091475085)
            ·
              refine ⟨1637632567488673909303157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4367020179969797091475085 1637632567488673909303157)
              ·
                refine ⟨153528053202063178997171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1637632567488673909303157 153528053202063178997171)
                ·
                  rfl

theorem cell21_2018215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 3, 5].length) (baseStart_2018215 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2018215 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2018215 prefixEnd_2018215 := by exact prefixLift 2018215
  have htrace : WordTrace (prefixWord ++ tailWord_2018215) baseStart_2018215 baseEnd_2018215 := by
    simpa [prefixWord, tailWord_2018215, baseEnd_2018215] using wordTrace_append hprefix tailTrace_2018215
  have hstable : (prefixWord ++ tailWord_2018215).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2018215).length < 2 ^ (prefixWord ++ tailWord_2018215).sum := by decide
  have hdescent : baseEnd_2018215 < baseStart_2018215 := by decide
  rcases family_descends (prefixWord ++ tailWord_2018215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2018305 : List Nat := [1, 2, 4, 1, 2, 4, 1, 1, 5]
def baseStart_2018305 : Nat := 118140960795 + 2018305 * 2 ^ 59
def prefixEnd_2018305 : Nat := 4983230072969 + 3 ^ 40 * 2018305 * 2
def baseEnd_2018305 : Nat := 460604698832369380491329

theorem tailTrace_2018305 : CollatzResearch.WordTrace tailWord_2018305 prefixEnd_2018305 460604698832369380491329 := by
  unfold tailWord_2018305
  simp only [CollatzResearch.WordTrace]
  refine ⟨73613630953033158896216369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49075753968688772597477579 73613630953033158896216369)
  ·
    refine ⟨55210223214774869172162277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73613630953033158896216369 55210223214774869172162277)
    ·
      refine ⟨10351916852770287969780427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55210223214774869172162277 10351916852770287969780427)
      ·
        refine ⟨15527875279155431954670641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10351916852770287969780427 15527875279155431954670641)
        ·
          refine ⟨11645906459366573966002981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15527875279155431954670641 11645906459366573966002981)
          ·
            refine ⟨2183607461131232618625559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11645906459366573966002981 2183607461131232618625559)
            ·
              refine ⟨3275411191696848927938339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2183607461131232618625559 3275411191696848927938339)
              ·
                refine ⟨4913116787545273391907509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3275411191696848927938339 4913116787545273391907509)
                ·
                  refine ⟨460604698832369380491329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4913116787545273391907509 460604698832369380491329)
                  ·
                    rfl

theorem cell21_2018305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 1, 1, 5].length) (baseStart_2018305 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2018305 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2018305 prefixEnd_2018305 := by exact prefixLift 2018305
  have htrace : WordTrace (prefixWord ++ tailWord_2018305) baseStart_2018305 baseEnd_2018305 := by
    simpa [prefixWord, tailWord_2018305, baseEnd_2018305] using wordTrace_append hprefix tailTrace_2018305
  have hstable : (prefixWord ++ tailWord_2018305).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2018305).length < 2 ^ (prefixWord ++ tailWord_2018305).sum := by decide
  have hdescent : baseEnd_2018305 < baseStart_2018305 := by decide
  rcases family_descends (prefixWord ++ tailWord_2018305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2018356 : List Nat := [2, 5, 1, 2, 1, 3, 2, 2, 3]
def baseStart_2018356 : Nat := 118140960795 + 2018356 * 2 ^ 59
def prefixEnd_2018356 : Nat := 4983230072969 + 3 ^ 40 * 2018356 * 2
def baseEnd_2018356 : Nat := 460616337727204625141225

theorem tailTrace_2018356 : CollatzResearch.WordTrace tailWord_2018356 prefixEnd_2018356 460616337727204625141225 := by
  unfold tailWord_2018356
  simp only [CollatzResearch.WordTrace]
  refine ⟨36807745537924197303161461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49076994050565596404215281 36807745537924197303161461)
  ·
    refine ⟨3450726144180393497171387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 36807745537924197303161461 3450726144180393497171387)
    ·
      refine ⟨5176089216270590245757081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3450726144180393497171387 5176089216270590245757081)
      ·
        refine ⟨3882066912202942684317811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5176089216270590245757081 3882066912202942684317811)
        ·
          refine ⟨5823100368304414026476717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3882066912202942684317811 5823100368304414026476717)
          ·
            refine ⟨2183662638114155259928769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5823100368304414026476717 2183662638114155259928769)
            ·
              refine ⟨1637746978585616444946577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2183662638114155259928769 1637746978585616444946577)
              ·
                refine ⟨1228310233939212333709933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1637746978585616444946577 1228310233939212333709933)
                ·
                  refine ⟨460616337727204625141225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1228310233939212333709933 460616337727204625141225)
                  ·
                    rfl

theorem cell21_2018356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 2, 2, 3].length) (baseStart_2018356 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2018356 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2018356 prefixEnd_2018356 := by exact prefixLift 2018356
  have htrace : WordTrace (prefixWord ++ tailWord_2018356) baseStart_2018356 baseEnd_2018356 := by
    simpa [prefixWord, tailWord_2018356, baseEnd_2018356] using wordTrace_append hprefix tailTrace_2018356
  have hstable : (prefixWord ++ tailWord_2018356).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2018356).length < 2 ^ (prefixWord ++ tailWord_2018356).sum := by decide
  have hdescent : baseEnd_2018356 < baseStart_2018356 := by decide
  rcases family_descends (prefixWord ++ tailWord_2018356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2018381 : List Nat := [1, 6, 1, 1, 1, 3, 1, 2, 5]
def baseStart_2018381 : Nat := 118140960795 + 2018381 * 2 ^ 59
def prefixEnd_2018381 : Nat := 4983230072969 + 3 ^ 40 * 2018381 * 2
def baseEnd_2018381 : Nat := 460622043067810137224507

theorem tailTrace_2018381 : CollatzResearch.WordTrace tailWord_2018381 prefixEnd_2018381 460622043067810137224507 := by
  unfold tailWord_2018381
  simp only [CollatzResearch.WordTrace]
  refine ⟨73616402900757823875982997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49077601933838549250655331 73616402900757823875982997)
  ·
    refine ⟨3450768885973022994186703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 73616402900757823875982997 3450768885973022994186703)
    ·
      refine ⟨5176153328959534491280055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3450768885973022994186703 5176153328959534491280055)
      ·
        refine ⟨7764229993439301736920083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5176153328959534491280055 7764229993439301736920083)
        ·
          refine ⟨11646344990158952605380125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7764229993439301736920083 11646344990158952605380125)
          ·
            refine ⟨4367379371309607227017547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11646344990158952605380125 4367379371309607227017547)
            ·
              refine ⟨6551069056964410840526321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4367379371309607227017547 6551069056964410840526321)
              ·
                refine ⟨4913301792723308130394741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6551069056964410840526321 4913301792723308130394741)
                ·
                  refine ⟨460622043067810137224507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4913301792723308130394741 460622043067810137224507)
                  ·
                    rfl

theorem cell21_2018381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 1, 2, 5].length) (baseStart_2018381 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2018381 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2018381 prefixEnd_2018381 := by exact prefixLift 2018381
  have htrace : WordTrace (prefixWord ++ tailWord_2018381) baseStart_2018381 baseEnd_2018381 := by
    simpa [prefixWord, tailWord_2018381, baseEnd_2018381] using wordTrace_append hprefix tailTrace_2018381
  have hstable : (prefixWord ++ tailWord_2018381).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2018381).length < 2 ^ (prefixWord ++ tailWord_2018381).sum := by decide
  have hdescent : baseEnd_2018381 < baseStart_2018381 := by decide
  rcases family_descends (prefixWord ++ tailWord_2018381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2018471 : List Nat := [1, 1, 6, 2, 1, 1, 2, 1, 6]
def baseStart_2018471 : Nat := 118140960795 + 2018471 * 2 ^ 59
def prefixEnd_2018471 : Nat := 4983230072969 + 3 ^ 40 * 2018471 * 2
def baseEnd_2018471 : Nat := 460642582293989980724323

theorem tailTrace_2018471 : CollatzResearch.WordTrace tailWord_2018471 prefixEnd_2018471 460642582293989980724323 := by
  unfold tailWord_2018471
  simp only [CollatzResearch.WordTrace]
  refine ⟨73619685470431769246759267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49079790313621179497839511 73619685470431769246759267)
  ·
    refine ⟨110429528205647653870138901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73619685470431769246759267 110429528205647653870138901)
    ·
      refine ⟨5176384134639733775162761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 110429528205647653870138901 5176384134639733775162761)
      ·
        refine ⟨3882288100979800331372071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5176384134639733775162761 3882288100979800331372071)
        ·
          refine ⟨5823432151469700497058107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3882288100979800331372071 5823432151469700497058107)
          ·
            refine ⟨8735148227204550745587161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5823432151469700497058107 8735148227204550745587161)
            ·
              refine ⟨6551361170403413059190371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8735148227204550745587161 6551361170403413059190371)
              ·
                refine ⟨9827041755605119588785557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6551361170403413059190371 9827041755605119588785557)
                ·
                  refine ⟨460642582293989980724323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9827041755605119588785557 460642582293989980724323)
                  ·
                    rfl

theorem cell21_2018471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 2, 1, 6].length) (baseStart_2018471 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2018471 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2018471 prefixEnd_2018471 := by exact prefixLift 2018471
  have htrace : WordTrace (prefixWord ++ tailWord_2018471) baseStart_2018471 baseEnd_2018471 := by
    simpa [prefixWord, tailWord_2018471, baseEnd_2018471] using wordTrace_append hprefix tailTrace_2018471
  have hstable : (prefixWord ++ tailWord_2018471).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2018471).length < 2 ^ (prefixWord ++ tailWord_2018471).sum := by decide
  have hdescent : baseEnd_2018471 < baseStart_2018471 := by decide
  rcases family_descends (prefixWord ++ tailWord_2018471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2018474 : List Nat := [3, 1, 5, 1, 1, 3, 1, 1, 5]
def baseStart_2018474 : Nat := 118140960795 + 2018474 * 2 ^ 59
def prefixEnd_2018474 : Nat := 4983230072969 + 3 ^ 40 * 2018474 * 2
def baseEnd_2018474 : Nat := 460643266934862642174317

theorem tailTrace_2018474 : CollatzResearch.WordTrace tailWord_2018474 prefixEnd_2018474 460643266934862642174317 := by
  unfold tailWord_2018474
  simp only [CollatzResearch.WordTrace]
  refine ⟨18404948722355225189779619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49079863259613933839412317 18404948722355225189779619)
  ·
    refine ⟨27607423083532837784669429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18404948722355225189779619 27607423083532837784669429)
    ·
      refine ⟨2588195914081203542312759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 27607423083532837784669429 2588195914081203542312759)
      ·
        refine ⟨3882293871121805313469139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2588195914081203542312759 3882293871121805313469139)
        ·
          refine ⟨5823440806682707970203709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3882293871121805313469139 5823440806682707970203709)
          ·
            refine ⟨2183790302506015488826391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5823440806682707970203709 2183790302506015488826391)
            ·
              refine ⟨3275685453759023233239587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2183790302506015488826391 3275685453759023233239587)
              ·
                refine ⟨4913528180638534849859381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3275685453759023233239587 4913528180638534849859381)
                ·
                  refine ⟨460643266934862642174317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4913528180638534849859381 460643266934862642174317)
                  ·
                    rfl

theorem cell21_2018474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 1, 1, 5].length) (baseStart_2018474 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2018474 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2018474 prefixEnd_2018474 := by exact prefixLift 2018474
  have htrace : WordTrace (prefixWord ++ tailWord_2018474) baseStart_2018474 baseEnd_2018474 := by
    simpa [prefixWord, tailWord_2018474, baseEnd_2018474] using wordTrace_append hprefix tailTrace_2018474
  have hstable : (prefixWord ++ tailWord_2018474).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2018474).length < 2 ^ (prefixWord ++ tailWord_2018474).sum := by decide
  have hdescent : baseEnd_2018474 < baseStart_2018474 := by decide
  rcases family_descends (prefixWord ++ tailWord_2018474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2018665 : List Nat := [1, 2, 1, 1, 1, 3, 2, 2, 8]
def baseStart_2018665 : Nat := 118140960795 + 2018665 * 2 ^ 59
def prefixEnd_2018665 : Nat := 4983230072969 + 3 ^ 40 * 2018665 * 2
def baseEnd_2018665 : Nat := 460686855737088754490593

theorem tailTrace_2018665 : CollatzResearch.WordTrace tailWord_2018665 prefixEnd_2018665 460686855737088754490593 := by
  unfold tailWord_2018665
  simp only [CollatzResearch.WordTrace]
  refine ⟨73626761231728940379321449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49084507487819293586214299 73626761231728940379321449)
  ·
    refine ⟨55220070923796705284491087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73626761231728940379321449 55220070923796705284491087)
    ·
      refine ⟨82830106385695057926736631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55220070923796705284491087 82830106385695057926736631)
      ·
        refine ⟨124245159578542586890104947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82830106385695057926736631 124245159578542586890104947)
        ·
          refine ⟨186367739367813880335157421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124245159578542586890104947 186367739367813880335157421)
          ·
            refine ⟨69887902262930205125684033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 186367739367813880335157421 69887902262930205125684033)
            ·
              refine ⟨52415926697197653844263025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69887902262930205125684033 52415926697197653844263025)
              ·
                refine ⟨39311945022898240383197269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52415926697197653844263025 39311945022898240383197269)
                ·
                  refine ⟨460686855737088754490593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39311945022898240383197269 460686855737088754490593)
                  ·
                    rfl

theorem cell21_2018665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 2, 8].length) (baseStart_2018665 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2018665 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2018665 prefixEnd_2018665 := by exact prefixLift 2018665
  have htrace : WordTrace (prefixWord ++ tailWord_2018665) baseStart_2018665 baseEnd_2018665 := by
    simpa [prefixWord, tailWord_2018665, baseEnd_2018665] using wordTrace_append hprefix tailTrace_2018665
  have hstable : (prefixWord ++ tailWord_2018665).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2018665).length < 2 ^ (prefixWord ++ tailWord_2018665).sum := by decide
  have hdescent : baseEnd_2018665 < baseStart_2018665 := by decide
  rcases family_descends (prefixWord ++ tailWord_2018665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2018696 : List Nat := [2, 1, 3, 3, 1, 11]
def baseStart_2018696 : Nat := 118140960795 + 2018696 * 2 ^ 59
def prefixEnd_2018696 : Nat := 4983230072969 + 3 ^ 40 * 2018696 * 2
def baseEnd_2018696 : Nat := 17062738161460725536069

theorem tailTrace_2018696 : CollatzResearch.WordTrace tailWord_2018696 prefixEnd_2018696 17062738161460725536069 := by
  unfold tailWord_2018696
  simp only [CollatzResearch.WordTrace]
  refine ⟨36813945947308316336849971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49085261263077755115799961 36813945947308316336849971)
  ·
    refine ⟨55220918920962474505274957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36813945947308316336849971 55220918920962474505274957)
    ·
      refine ⟨20707844595360927939478109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55220918920962474505274957 20707844595360927939478109)
      ·
        refine ⟨7765441723260347977304291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20707844595360927939478109 7765441723260347977304291)
        ·
          refine ⟨11648162584890521965956437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7765441723260347977304291 11648162584890521965956437)
          ·
            refine ⟨17062738161460725536069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 11648162584890521965956437 17062738161460725536069)
            ·
              rfl

theorem cell21_2018696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 11].length) (baseStart_2018696 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2018696 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2018696 prefixEnd_2018696 := by exact prefixLift 2018696
  have htrace : WordTrace (prefixWord ++ tailWord_2018696) baseStart_2018696 baseEnd_2018696 := by
    simpa [prefixWord, tailWord_2018696, baseEnd_2018696] using wordTrace_append hprefix tailTrace_2018696
  have hstable : (prefixWord ++ tailWord_2018696).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2018696).length < 2 ^ (prefixWord ++ tailWord_2018696).sum := by decide
  have hdescent : baseEnd_2018696 < baseStart_2018696 := by decide
  rcases family_descends (prefixWord ++ tailWord_2018696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2018702 : List Nat := [4, 1, 1, 4, 2, 1, 1, 4, 3]
def baseStart_2018702 : Nat := 118140960795 + 2018702 * 2 ^ 59
def prefixEnd_2018702 : Nat := 4983230072969 + 3 ^ 40 * 2018702 * 2
def baseEnd_2018702 : Nat := 460695299641184912373851

theorem tailTrace_2018702 : CollatzResearch.WordTrace tailWord_2018702 prefixEnd_2018702 460695299641184912373851 := by
  unfold tailWord_2018702
  simp only [CollatzResearch.WordTrace]
  refine ⟨9203513841574361962302295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49085407155063263798945573 9203513841574361962302295)
  ·
    refine ⟨13805270762361542943453443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9203513841574361962302295 13805270762361542943453443)
    ·
      refine ⟨20707906143542314415180165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13805270762361542943453443 20707906143542314415180165)
      ·
        refine ⟨3882732401914183952846281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20707906143542314415180165 3882732401914183952846281)
        ·
          refine ⟨2912049301435637964634711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3882732401914183952846281 2912049301435637964634711)
          ·
            refine ⟨4368073952153456946952067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2912049301435637964634711 4368073952153456946952067)
            ·
              refine ⟨6552110928230185420428101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4368073952153456946952067 6552110928230185420428101)
              ·
                refine ⟨1228520799043159766330269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6552110928230185420428101 1228520799043159766330269)
                ·
                  refine ⟨460695299641184912373851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1228520799043159766330269 460695299641184912373851)
                  ·
                    rfl

theorem cell21_2018702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 1, 4, 3].length) (baseStart_2018702 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2018702 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2018702 prefixEnd_2018702 := by exact prefixLift 2018702
  have htrace : WordTrace (prefixWord ++ tailWord_2018702) baseStart_2018702 baseEnd_2018702 := by
    simpa [prefixWord, tailWord_2018702, baseEnd_2018702] using wordTrace_append hprefix tailTrace_2018702
  have hstable : (prefixWord ++ tailWord_2018702).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2018702).length < 2 ^ (prefixWord ++ tailWord_2018702).sum := by decide
  have hdescent : baseEnd_2018702 < baseStart_2018702 := by decide
  rcases family_descends (prefixWord ++ tailWord_2018702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2018713 : List Nat := [1, 2, 1, 2, 1, 7, 1, 6]
def baseStart_2018713 : Nat := 118140960795 + 2018713 * 2 ^ 59
def prefixEnd_2018713 : Nat := 4983230072969 + 3 ^ 40 * 2018713 * 2
def baseEnd_2018713 : Nat := 153565936663683779230165

theorem tailTrace_2018713 : CollatzResearch.WordTrace tailWord_2018713 prefixEnd_2018713 153565936663683779230165 := by
  unfold tailWord_2018713
  simp only [CollatzResearch.WordTrace]
  refine ⟨73628511935555044577068793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49085674623703363051379195 73628511935555044577068793)
  ·
    refine ⟨55221383951666283432801595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73628511935555044577068793 55221383951666283432801595)
    ·
      refine ⟨82832075927499425149202393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55221383951666283432801595 82832075927499425149202393)
      ·
        refine ⟨62124056945624568861901795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82832075927499425149202393 62124056945624568861901795)
        ·
          refine ⟨93186085418436853292852693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62124056945624568861901795 93186085418436853292852693)
          ·
            refine ⟨2184048876994613749051235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 93186085418436853292852693 2184048876994613749051235)
            ·
              refine ⟨3276073315491920623576853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2184048876994613749051235 3276073315491920623576853)
              ·
                refine ⟨153565936663683779230165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3276073315491920623576853 153565936663683779230165)
                ·
                  rfl

theorem cell21_2018713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 1, 6].length) (baseStart_2018713 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2018713 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2018713 prefixEnd_2018713 := by exact prefixLift 2018713
  have htrace : WordTrace (prefixWord ++ tailWord_2018713) baseStart_2018713 baseEnd_2018713 := by
    simpa [prefixWord, tailWord_2018713, baseEnd_2018713] using wordTrace_append hprefix tailTrace_2018713
  have hstable : (prefixWord ++ tailWord_2018713).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2018713).length < 2 ^ (prefixWord ++ tailWord_2018713).sum := by decide
  have hdescent : baseEnd_2018713 < baseStart_2018713 := by decide
  rcases family_descends (prefixWord ++ tailWord_2018713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2018744 : List Nat := [2, 1, 2, 1, 2, 2, 3, 5, 3]
def baseStart_2018744 : Nat := 118140960795 + 2018744 * 2 ^ 59
def prefixEnd_2018744 : Nat := 4983230072969 + 3 ^ 40 * 2018744 * 2
def baseEnd_2018744 : Nat := 460704884613402172673765

theorem tailTrace_2018744 : CollatzResearch.WordTrace tailWord_2018744 prefixEnd_2018744 460704884613402172673765 := by
  unfold tailWord_2018744
  simp only [CollatzResearch.WordTrace]
  refine ⟨36814821299221368435723643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49086428398961824580964857 36814821299221368435723643)
  ·
    refine ⟨55222231948832052653585465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36814821299221368435723643 55222231948832052653585465)
    ·
      refine ⟨41416673961624039490189099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55222231948832052653585465 41416673961624039490189099)
      ·
        refine ⟨62125010942436059235283649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41416673961624039490189099 62125010942436059235283649)
        ·
          refine ⟨46593758206827044426462737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62125010942436059235283649 46593758206827044426462737)
          ·
            refine ⟨34945318655120283319847053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46593758206827044426462737 34945318655120283319847053)
            ·
              refine ⟨13104494495670106244942645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34945318655120283319847053 13104494495670106244942645)
              ·
                refine ⟨1228546358969072460463373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13104494495670106244942645 1228546358969072460463373)
                ·
                  refine ⟨460704884613402172673765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1228546358969072460463373 460704884613402172673765)
                  ·
                    rfl

theorem cell21_2018744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 5, 3].length) (baseStart_2018744 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2018744 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2018744 prefixEnd_2018744 := by exact prefixLift 2018744
  have htrace : WordTrace (prefixWord ++ tailWord_2018744) baseStart_2018744 baseEnd_2018744 := by
    simpa [prefixWord, tailWord_2018744, baseEnd_2018744] using wordTrace_append hprefix tailTrace_2018744
  have hstable : (prefixWord ++ tailWord_2018744).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2018744).length < 2 ^ (prefixWord ++ tailWord_2018744).sum := by decide
  have hdescent : baseEnd_2018744 < baseStart_2018744 := by decide
  rcases family_descends (prefixWord ++ tailWord_2018744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2018789 : List Nat := [1, 3, 1, 5, 1, 2, 1, 7]
def baseStart_2018789 : Nat := 118140960795 + 2018789 * 2 ^ 59
def prefixEnd_2018789 : Nat := 4983230072969 + 3 ^ 40 * 2018789 * 2
def baseEnd_2018789 : Nat := 153571718075497364807891

theorem tailTrace_2018789 : CollatzResearch.WordTrace tailWord_2018789 prefixEnd_2018789 153571718075497364807891 := by
  unfold tailWord_2018789
  simp only [CollatzResearch.WordTrace]
  refine ⟨73631283883279709556835421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49087522588853139704556947 73631283883279709556835421)
  ·
    refine ⟨27611731456229891083813283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73631283883279709556835421 27611731456229891083813283)
    ·
      refine ⟨41417597184344836625719925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27611731456229891083813283 41417597184344836625719925)
      ·
        refine ⟨3882899736032328433661243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 41417597184344836625719925 3882899736032328433661243)
        ·
          refine ⟨5824349604048492650491865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3882899736032328433661243 5824349604048492650491865)
          ·
            refine ⟨4368262203036369487868899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5824349604048492650491865 4368262203036369487868899)
            ·
              refine ⟨6552393304554554231803349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4368262203036369487868899 6552393304554554231803349)
              ·
                refine ⟨153571718075497364807891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6552393304554554231803349 153571718075497364807891)
                ·
                  rfl

theorem cell21_2018789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 1, 7].length) (baseStart_2018789 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2018789 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2018789 prefixEnd_2018789 := by exact prefixLift 2018789
  have htrace : WordTrace (prefixWord ++ tailWord_2018789) baseStart_2018789 baseEnd_2018789 := by
    simpa [prefixWord, tailWord_2018789, baseEnd_2018789] using wordTrace_append hprefix tailTrace_2018789
  have hstable : (prefixWord ++ tailWord_2018789).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2018789).length < 2 ^ (prefixWord ++ tailWord_2018789).sum := by decide
  have hdescent : baseEnd_2018789 < baseStart_2018789 := by decide
  rcases family_descends (prefixWord ++ tailWord_2018789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2018958 : List Nat := [4, 1, 1, 3, 1, 4, 2, 5]
def baseStart_2018958 : Nat := 118140960795 + 2018958 * 2 ^ 59
def prefixEnd_2018958 : Nat := 4983230072969 + 3 ^ 40 * 2018958 * 2
def baseEnd_2018958 : Nat := 153584574109661785368887

theorem tailTrace_2018958 : CollatzResearch.WordTrace tailWord_2018958 prefixEnd_2018958 153584574109661785368887 := by
  unfold tailWord_2018958
  simp only [CollatzResearch.WordTrace]
  refine ⟨9204680977458431427467191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49091631879778300946491685 9204680977458431427467191)
  ·
    refine ⟨13807021466187647141200787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9204680977458431427467191 13807021466187647141200787)
    ·
      refine ⟨20710532199281470711801181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13807021466187647141200787 20710532199281470711801181)
      ·
        refine ⟨7766449574730551516925443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20710532199281470711801181 7766449574730551516925443)
        ·
          refine ⟨11649674362095827275388165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7766449574730551516925443 11649674362095827275388165)
          ·
            refine ⟨2184313942892967614135281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11649674362095827275388165 2184313942892967614135281)
            ·
              refine ⟨1638235457169725710601461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2184313942892967614135281 1638235457169725710601461)
              ·
                refine ⟨153584574109661785368887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1638235457169725710601461 153584574109661785368887)
                ·
                  rfl

theorem cell21_2018958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 2, 5].length) (baseStart_2018958 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2018958 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2018958 prefixEnd_2018958 := by exact prefixLift 2018958
  have htrace : WordTrace (prefixWord ++ tailWord_2018958) baseStart_2018958 baseEnd_2018958 := by
    simpa [prefixWord, tailWord_2018958, baseEnd_2018958] using wordTrace_append hprefix tailTrace_2018958
  have hstable : (prefixWord ++ tailWord_2018958).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2018958).length < 2 ^ (prefixWord ++ tailWord_2018958).sum := by decide
  have hdescent : baseEnd_2018958 < baseStart_2018958 := by decide
  rcases family_descends (prefixWord ++ tailWord_2018958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2019124 : List Nat := [2, 5, 1, 1, 2, 1, 2, 2, 5]
def baseStart_2019124 : Nat := 118140960795 + 2019124 * 2 ^ 59
def prefixEnd_2019124 : Nat := 4983230072969 + 3 ^ 40 * 2019124 * 2
def baseEnd_2019124 : Nat := 460791605790605956339655

theorem tailTrace_2019124 : CollatzResearch.WordTrace tailWord_2019124 prefixEnd_2019124 460791605790605956339655 := by
  unfold tailWord_2019124
  simp only [CollatzResearch.WordTrace]
  refine ⟨36821751168533030885140213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49095668224710707846853617 36821751168533030885140213)
  ·
    refine ⟨3452039172049971645481895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 36821751168533030885140213 3452039172049971645481895)
    ·
      refine ⟨5178058758074957468222843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3452039172049971645481895 5178058758074957468222843)
      ·
        refine ⟨7767088137112436202334265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5178058758074957468222843 7767088137112436202334265)
        ·
          refine ⟨5825316102834327151750699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7767088137112436202334265 5825316102834327151750699)
          ·
            refine ⟨8737974154251490727626049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5825316102834327151750699 8737974154251490727626049)
            ·
              refine ⟨6553480615688618045719537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8737974154251490727626049 6553480615688618045719537)
              ·
                refine ⟨4915110461766463534289653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6553480615688618045719537 4915110461766463534289653)
                ·
                  refine ⟨460791605790605956339655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4915110461766463534289653 460791605790605956339655)
                  ·
                    rfl

theorem cell21_2019124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 2, 2, 5].length) (baseStart_2019124 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2019124 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2019124 prefixEnd_2019124 := by exact prefixLift 2019124
  have htrace : WordTrace (prefixWord ++ tailWord_2019124) baseStart_2019124 baseEnd_2019124 := by
    simpa [prefixWord, tailWord_2019124, baseEnd_2019124] using wordTrace_append hprefix tailTrace_2019124
  have hstable : (prefixWord ++ tailWord_2019124).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2019124).length < 2 ^ (prefixWord ++ tailWord_2019124).sum := by decide
  have hdescent : baseEnd_2019124 < baseStart_2019124 := by decide
  rcases family_descends (prefixWord ++ tailWord_2019124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2019172 : List Nat := [2, 3, 1, 1, 5, 2, 2, 1, 4]
def baseStart_2019172 : Nat := 118140960795 + 2019172 * 2 ^ 59
def prefixEnd_2019172 : Nat := 4983230072969 + 3 ^ 40 * 2019172 * 2
def baseEnd_2019172 : Nat := 460802560044568539539557

theorem tailTrace_2019172 : CollatzResearch.WordTrace tailWord_2019172 prefixEnd_2019172 460802560044568539539557 := by
  unfold tailWord_2019172
  simp only [CollatzResearch.WordTrace]
  refine ⟨36822626520446082984013885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49096835360594777312018513 36822626520446082984013885)
  ·
    refine ⟨13808484945167281119005207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36822626520446082984013885 13808484945167281119005207)
    ·
      refine ⟨20712727417750921678507811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13808484945167281119005207 20712727417750921678507811)
      ·
        refine ⟨31069091126626382517761717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20712727417750921678507811 31069091126626382517761717)
        ·
          refine ⟨2912727293121223361040161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31069091126626382517761717 2912727293121223361040161)
          ·
            refine ⟨2184545469840917520780121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2912727293121223361040161 2184545469840917520780121)
            ·
              refine ⟨1638409102380688140585091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2184545469840917520780121 1638409102380688140585091)
              ·
                refine ⟨2457613653571032210877637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1638409102380688140585091 2457613653571032210877637)
                ·
                  refine ⟨460802560044568539539557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2457613653571032210877637 460802560044568539539557)
                  ·
                    rfl

theorem cell21_2019172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 2, 1, 4].length) (baseStart_2019172 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2019172 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2019172 prefixEnd_2019172 := by exact prefixLift 2019172
  have htrace : WordTrace (prefixWord ++ tailWord_2019172) baseStart_2019172 baseEnd_2019172 := by
    simpa [prefixWord, tailWord_2019172, baseEnd_2019172] using wordTrace_append hprefix tailTrace_2019172
  have hstable : (prefixWord ++ tailWord_2019172).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2019172).length < 2 ^ (prefixWord ++ tailWord_2019172).sum := by decide
  have hdescent : baseEnd_2019172 < baseStart_2019172 := by decide
  rcases family_descends (prefixWord ++ tailWord_2019172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2019259 : List Nat := [1, 1, 1, 1, 1, 2, 2, 9, 3]
def baseStart_2019259 : Nat := 118140960795 + 2019259 * 2 ^ 59
def prefixEnd_2019259 : Nat := 4983230072969 + 3 ^ 40 * 2019259 * 2
def baseEnd_2019259 : Nat := 460822414629875721589379

theorem tailTrace_2019259 : CollatzResearch.WordTrace tailWord_2019259 prefixEnd_2019259 460822414629875721589379 := by
  unfold tailWord_2019259
  simp only [CollatzResearch.WordTrace]
  refine ⟨73648426191576979826444831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49098950794384653217629887 73648426191576979826444831)
  ·
    refine ⟨110472639287365469739667247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73648426191576979826444831 110472639287365469739667247)
    ·
      refine ⟨165708958931048204609500871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110472639287365469739667247 165708958931048204609500871)
      ·
        refine ⟨248563438396572306914251307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165708958931048204609500871 248563438396572306914251307)
        ·
          refine ⟨372845157594858460371376961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248563438396572306914251307 372845157594858460371376961)
          ·
            refine ⟨279633868196143845278532721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 372845157594858460371376961 279633868196143845278532721)
            ·
              refine ⟨209725401147107883958899541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 279633868196143845278532721 209725401147107883958899541)
              ·
                refine ⟨1228859772346335257571677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 209725401147107883958899541 1228859772346335257571677)
                ·
                  refine ⟨460822414629875721589379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1228859772346335257571677 460822414629875721589379)
                  ·
                    rfl

theorem cell21_2019259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 9, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 9, 3].length) (baseStart_2019259 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2019259 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2019259 prefixEnd_2019259 := by exact prefixLift 2019259
  have htrace : WordTrace (prefixWord ++ tailWord_2019259) baseStart_2019259 baseEnd_2019259 := by
    simpa [prefixWord, tailWord_2019259, baseEnd_2019259] using wordTrace_append hprefix tailTrace_2019259
  have hstable : (prefixWord ++ tailWord_2019259).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2019259).length < 2 ^ (prefixWord ++ tailWord_2019259).sum := by decide
  have hdescent : baseEnd_2019259 < baseStart_2019259 := by decide
  rcases family_descends (prefixWord ++ tailWord_2019259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2019276 : List Nat := [2, 2, 1, 4, 1, 2, 2, 4, 3]
def baseStart_2019276 : Nat := 118140960795 + 2019276 * 2 ^ 59
def prefixEnd_2019276 : Nat := 4983230072969 + 3 ^ 40 * 2019276 * 2
def baseEnd_2019276 : Nat := 460826294261487469806011

theorem tailTrace_2019276 : CollatzResearch.WordTrace tailWord_2019276 prefixEnd_2019276 460826294261487469806011 := by
  unfold tailWord_2019276
  simp only [CollatzResearch.WordTrace]
  refine ⟨36824523116257695864906841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49099364155010261153209121 36824523116257695864906841)
  ·
    refine ⟨27618392337193271898680131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36824523116257695864906841 27618392337193271898680131)
    ·
      refine ⟨41427588505789907848020197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27618392337193271898680131 41427588505789907848020197)
      ·
        refine ⟨7767672844835607721503787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41427588505789907848020197 7767672844835607721503787)
        ·
          refine ⟨11651509267253411582255681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7767672844835607721503787 11651509267253411582255681)
          ·
            refine ⟨8738631950440058686691761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11651509267253411582255681 8738631950440058686691761)
            ·
              refine ⟨6553973962830044015018821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8738631950440058686691761 6553973962830044015018821)
              ·
                refine ⟨1228870118030633252816029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6553973962830044015018821 1228870118030633252816029)
                ·
                  refine ⟨460826294261487469806011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1228870118030633252816029 460826294261487469806011)
                  ·
                    rfl

theorem cell21_2019276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 2, 4, 3].length) (baseStart_2019276 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2019276 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2019276 prefixEnd_2019276 := by exact prefixLift 2019276
  have htrace : WordTrace (prefixWord ++ tailWord_2019276) baseStart_2019276 baseEnd_2019276 := by
    simpa [prefixWord, tailWord_2019276, baseEnd_2019276] using wordTrace_append hprefix tailTrace_2019276
  have hstable : (prefixWord ++ tailWord_2019276).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2019276).length < 2 ^ (prefixWord ++ tailWord_2019276).sum := by decide
  have hdescent : baseEnd_2019276 < baseStart_2019276 := by decide
  rcases family_descends (prefixWord ++ tailWord_2019276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2019287 : List Nat := [1, 1, 3, 2, 1, 1, 4, 8]
def baseStart_2019287 : Nat := 118140960795 + 2019287 * 2 ^ 59
def prefixEnd_2019287 : Nat := 4983230072969 + 3 ^ 40 * 2019287 * 2
def baseEnd_2019287 : Nat := 153609601537117965040885

theorem tailTrace_2019287 : CollatzResearch.WordTrace tailWord_2019287 prefixEnd_2019287 153609601537117965040885 := by
  unfold tailWord_2019287
  simp only [CollatzResearch.WordTrace]
  refine ⟨73649447435475540608464115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49099631623650360405642743 73649447435475540608464115)
  ·
    refine ⟨110474171153213310912696173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73649447435475540608464115 110474171153213310912696173)
    ·
      refine ⟨41427814182454991592261065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110474171153213310912696173 41427814182454991592261065)
      ·
        refine ⟨31070860636841243694195799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41427814182454991592261065 31070860636841243694195799)
        ·
          refine ⟨46606290955261865541293699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31070860636841243694195799 46606290955261865541293699)
          ·
            refine ⟨69909436432892798311940549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46606290955261865541293699 69909436432892798311940549)
            ·
              refine ⟨13108019331167399683488853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69909436432892798311940549 13108019331167399683488853)
              ·
                refine ⟨153609601537117965040885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13108019331167399683488853 153609601537117965040885)
                ·
                  rfl

theorem cell21_2019287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 8].length) (baseStart_2019287 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2019287 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2019287 prefixEnd_2019287 := by exact prefixLift 2019287
  have htrace : WordTrace (prefixWord ++ tailWord_2019287) baseStart_2019287 baseEnd_2019287 := by
    simpa [prefixWord, tailWord_2019287, baseEnd_2019287] using wordTrace_append hprefix tailTrace_2019287
  have hstable : (prefixWord ++ tailWord_2019287).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2019287).length < 2 ^ (prefixWord ++ tailWord_2019287).sum := by decide
  have hdescent : baseEnd_2019287 < baseStart_2019287 := by decide
  rcases family_descends (prefixWord ++ tailWord_2019287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2019335 : List Nat := [1, 1, 4, 3, 1, 2, 3, 1, 5]
def baseStart_2019335 : Nat := 118140960795 + 2019335 * 2 ^ 59
def prefixEnd_2019335 : Nat := 4983230072969 + 3 ^ 40 * 2019335 * 2
def baseEnd_2019335 : Nat := 460839758865316478322557

theorem tailTrace_2019335 : CollatzResearch.WordTrace tailWord_2019335 prefixEnd_2019335 460839758865316478322557 := by
  unfold tailWord_2019335
  simp only [CollatzResearch.WordTrace]
  refine ⟨73651198139301644806211459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49100798759534429870807639 73651198139301644806211459)
  ·
    refine ⟨110476797208952467209317189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73651198139301644806211459 110476797208952467209317189)
    ·
      refine ⟨20714399476678587601746973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 110476797208952467209317189 20714399476678587601746973)
      ·
        refine ⟨7767899803754470350655115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20714399476678587601746973 7767899803754470350655115)
        ·
          refine ⟨11651849705631705525982673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7767899803754470350655115 11651849705631705525982673)
          ·
            refine ⟨8738887279223779144487005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11651849705631705525982673 8738887279223779144487005)
            ·
              refine ⟨3277082729708917179182627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8738887279223779144487005 3277082729708917179182627)
              ·
                refine ⟨4915624094563375768773941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3277082729708917179182627 4915624094563375768773941)
                ·
                  refine ⟨460839758865316478322557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4915624094563375768773941 460839758865316478322557)
                  ·
                    rfl

theorem cell21_2019335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 3, 1, 5].length) (baseStart_2019335 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2019335 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2019335 prefixEnd_2019335 := by exact prefixLift 2019335
  have htrace : WordTrace (prefixWord ++ tailWord_2019335) baseStart_2019335 baseEnd_2019335 := by
    simpa [prefixWord, tailWord_2019335, baseEnd_2019335] using wordTrace_append hprefix tailTrace_2019335
  have hstable : (prefixWord ++ tailWord_2019335).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2019335).length < 2 ^ (prefixWord ++ tailWord_2019335).sum := by decide
  have hdescent : baseEnd_2019335 < baseStart_2019335 := by decide
  rcases family_descends (prefixWord ++ tailWord_2019335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2019341 : List Nat := [1, 7, 1, 2, 1, 1, 1, 3, 4]
def baseStart_2019341 : Nat := 118140960795 + 2019341 * 2 ^ 59
def prefixEnd_2019341 : Nat := 4983230072969 + 3 ^ 40 * 2019341 * 2
def baseEnd_2019341 : Nat := 460841128147061801222545

theorem tailTrace_2019341 : CollatzResearch.WordTrace tailWord_2019341 prefixEnd_2019341 460841128147061801222545 := by
  unfold tailWord_2019341
  simp only [CollatzResearch.WordTrace]
  refine ⟨73651416977279907830929877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49100944651519938553953251 73651416977279907830929877)
  ·
    refine ⟨1726205085404997839787419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 73651416977279907830929877 1726205085404997839787419)
    ·
      refine ⟨2589307628107496759681129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1726205085404997839787419 2589307628107496759681129)
      ·
        refine ⟨1941980721080622569760847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2589307628107496759681129 1941980721080622569760847)
        ·
          refine ⟨2912971081620933854641271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1941980721080622569760847 2912971081620933854641271)
          ·
            refine ⟨4369456622431400781961907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2912971081620933854641271 4369456622431400781961907)
            ·
              refine ⟨6554184933647101172942861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4369456622431400781961907 6554184933647101172942861)
              ·
                refine ⟨2457819350117662939853573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6554184933647101172942861 2457819350117662939853573)
                ·
                  refine ⟨460841128147061801222545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2457819350117662939853573 460841128147061801222545)
                  ·
                    rfl

theorem cell21_2019341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 1, 3, 4].length) (baseStart_2019341 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2019341 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2019341 prefixEnd_2019341 := by exact prefixLift 2019341
  have htrace : WordTrace (prefixWord ++ tailWord_2019341) baseStart_2019341 baseEnd_2019341 := by
    simpa [prefixWord, tailWord_2019341, baseEnd_2019341] using wordTrace_append hprefix tailTrace_2019341
  have hstable : (prefixWord ++ tailWord_2019341).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2019341).length < 2 ^ (prefixWord ++ tailWord_2019341).sum := by decide
  have hdescent : baseEnd_2019341 < baseStart_2019341 := by decide
  rcases family_descends (prefixWord ++ tailWord_2019341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2019363 : List Nat := [1, 1, 1, 4, 3, 1, 1, 9]
def baseStart_2019363 : Nat := 118140960795 + 2019363 * 2 ^ 59
def prefixEnd_2019363 : Nat := 4983230072969 + 3 ^ 40 * 2019363 * 2
def baseEnd_2019363 : Nat := 153615382948931550618611

theorem tailTrace_2019363 : CollatzResearch.WordTrace tailWord_2019363 prefixEnd_2019363 153615382948931550618611 := by
  unfold tailWord_2019363
  simp only [CollatzResearch.WordTrace]
  refine ⟨73652219383200205588230743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49101479588800137058820495 73652219383200205588230743)
  ·
    refine ⟨110478329074800308382346115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73652219383200205588230743 110478329074800308382346115)
    ·
      refine ⟨165717493612200462573519173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110478329074800308382346115 165717493612200462573519173)
      ·
        refine ⟨31072030052287586732534845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 165717493612200462573519173 31072030052287586732534845)
        ·
          refine ⟨11652011269607845024700567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31072030052287586732534845 11652011269607845024700567)
          ·
            refine ⟨17478016904411767537050851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11652011269607845024700567 17478016904411767537050851)
            ·
              refine ⟨26217025356617651305576277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17478016904411767537050851 26217025356617651305576277)
              ·
                refine ⟨153615382948931550618611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 26217025356617651305576277 153615382948931550618611)
                ·
                  rfl

theorem cell21_2019363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 9].length) (baseStart_2019363 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2019363 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2019363 prefixEnd_2019363 := by exact prefixLift 2019363
  have htrace : WordTrace (prefixWord ++ tailWord_2019363) baseStart_2019363 baseEnd_2019363 := by
    simpa [prefixWord, tailWord_2019363, baseEnd_2019363] using wordTrace_append hprefix tailTrace_2019363
  have hstable : (prefixWord ++ tailWord_2019363).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2019363).length < 2 ^ (prefixWord ++ tailWord_2019363).sum := by decide
  have hdescent : baseEnd_2019363 < baseStart_2019363 := by decide
  rcases family_descends (prefixWord ++ tailWord_2019363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2019380 : List Nat := [2, 5, 1, 2, 11]
def baseStart_2019380 : Nat := 118140960795 + 2019380 * 2 ^ 59
def prefixEnd_2019380 : Nat := 4983230072969 + 3 ^ 40 * 2019380 * 2
def baseEnd_2019380 : Nat := 5689506524424770371265

theorem tailTrace_2019380 : CollatzResearch.WordTrace tailWord_2019380 prefixEnd_2019380 5689506524424770371265 := by
  unfold tailWord_2019380
  simp only [CollatzResearch.WordTrace]
  refine ⟨36826419712069308745799797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49101892949425744994399729 36826419712069308745799797)
  ·
    refine ⟨3452476848006497694918731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 36826419712069308745799797 3452476848006497694918731)
    ·
      refine ⟨5178715272009746542378097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3452476848006497694918731 5178715272009746542378097)
      ·
        refine ⟨3884036454007309906783573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5178715272009746542378097 3884036454007309906783573)
        ·
          refine ⟨5689506524424770371265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 3884036454007309906783573 5689506524424770371265)
          ·
            rfl

theorem cell21_2019380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 11].length) (baseStart_2019380 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2019380 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2019380 prefixEnd_2019380 := by exact prefixLift 2019380
  have htrace : WordTrace (prefixWord ++ tailWord_2019380) baseStart_2019380 baseEnd_2019380 := by
    simpa [prefixWord, tailWord_2019380, baseEnd_2019380] using wordTrace_append hprefix tailTrace_2019380
  have hstable : (prefixWord ++ tailWord_2019380).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2019380).length < 2 ^ (prefixWord ++ tailWord_2019380).sum := by decide
  have hdescent : baseEnd_2019380 < baseStart_2019380 := by decide
  rcases family_descends (prefixWord ++ tailWord_2019380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2019408 : List Nat := [2, 1, 1, 1, 1, 3, 1, 1, 10]
def baseStart_2019408 : Nat := 118140960795 + 2019408 * 2 ^ 59
def prefixEnd_2019408 : Nat := 4983230072969 + 3 ^ 40 * 2019408 * 2
def baseEnd_2019408 : Nat := 460856418459884573605741

theorem tailTrace_2019408 : CollatzResearch.WordTrace tailWord_2019408 prefixEnd_2019408 460856418459884573605741 := by
  unfold tailWord_2019408
  simp only [CollatzResearch.WordTrace]
  refine ⟨36826930334018589136809439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49102573778691452182412585 36826930334018589136809439)
  ·
    refine ⟨55240395501027883705214159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36826930334018589136809439 55240395501027883705214159)
    ·
      refine ⟨82860593251541825557821239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55240395501027883705214159 82860593251541825557821239)
      ·
        refine ⟨124290889877312738336731859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82860593251541825557821239 124290889877312738336731859)
        ·
          refine ⟨186436334815969107505097789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124290889877312738336731859 186436334815969107505097789)
          ·
            refine ⟨69913625555988415314411671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 186436334815969107505097789 69913625555988415314411671)
            ·
              refine ⟨104870438333982622971617507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69913625555988415314411671 104870438333982622971617507)
              ·
                refine ⟨157305657500973934457426261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104870438333982622971617507 157305657500973934457426261)
                ·
                  refine ⟨460856418459884573605741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 157305657500973934457426261 460856418459884573605741)
                  ·
                    rfl

theorem cell21_2019408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 10].length) (baseStart_2019408 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2019408 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2019408 prefixEnd_2019408 := by exact prefixLift 2019408
  have htrace : WordTrace (prefixWord ++ tailWord_2019408) baseStart_2019408 baseEnd_2019408 := by
    simpa [prefixWord, tailWord_2019408, baseEnd_2019408] using wordTrace_append hprefix tailTrace_2019408
  have hstable : (prefixWord ++ tailWord_2019408).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2019408).length < 2 ^ (prefixWord ++ tailWord_2019408).sum := by decide
  have hdescent : baseEnd_2019408 < baseStart_2019408 := by decide
  rcases family_descends (prefixWord ++ tailWord_2019408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2019439 : List Nat := [1, 1, 2, 1, 3, 5, 8]
def baseStart_2019439 : Nat := 118140960795 + 2019439 * 2 ^ 59
def prefixEnd_2019439 : Nat := 4983230072969 + 3 ^ 40 * 2019439 * 2
def baseEnd_2019439 : Nat := 51207054786915045398779

theorem tailTrace_2019439 : CollatzResearch.WordTrace tailWord_2019439 prefixEnd_2019439 51207054786915045398779 := by
  unfold tailWord_2019439
  simp only [CollatzResearch.WordTrace]
  refine ⟨73654991330924870567997371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49103327553949913711998247 73654991330924870567997371)
  ·
    refine ⟨110482486996387305851996057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73654991330924870567997371 110482486996387305851996057)
    ·
      refine ⟨82861865247290479388997043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110482486996387305851996057 82861865247290479388997043)
      ·
        refine ⟨124292797870935719083495565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82861865247290479388997043 124292797870935719083495565)
        ·
          refine ⟨46609799201600894656310837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124292797870935719083495565 46609799201600894656310837)
          ·
            refine ⟨4369668675150083874029141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 46609799201600894656310837 4369668675150083874029141)
            ·
              refine ⟨51207054786915045398779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4369668675150083874029141 51207054786915045398779)
              ·
                rfl

theorem cell21_2019439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 8].length) (baseStart_2019439 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2019439 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2019439 prefixEnd_2019439 := by exact prefixLift 2019439
  have htrace : WordTrace (prefixWord ++ tailWord_2019439) baseStart_2019439 baseEnd_2019439 := by
    simpa [prefixWord, tailWord_2019439, baseEnd_2019439] using wordTrace_append hprefix tailTrace_2019439
  have hstable : (prefixWord ++ tailWord_2019439).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2019439).length < 2 ^ (prefixWord ++ tailWord_2019439).sum := by decide
  have hdescent : baseEnd_2019439 < baseStart_2019439 := by decide
  rcases family_descends (prefixWord ++ tailWord_2019439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2019442 : List Nat := [3, 2, 1, 2, 2, 2, 3, 2, 4]
def baseStart_2019442 : Nat := 118140960795 + 2019442 * 2 ^ 59
def prefixEnd_2019442 : Nat := 4983230072969 + 3 ^ 40 * 2019442 * 2
def baseEnd_2019442 : Nat := 460864177723108070039005

theorem tailTrace_2019442 : CollatzResearch.WordTrace tailWord_2019442 prefixEnd_2019442 460864177723108070039005 := by
  unfold tailWord_2019442
  simp only [CollatzResearch.WordTrace]
  refine ⟨18413775187478500520089145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49103400499942668053571053 18413775187478500520089145)
  ·
    refine ⟨13810331390608875390066859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18413775187478500520089145 13810331390608875390066859)
    ·
      refine ⟨20715497085913313085100289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13810331390608875390066859 20715497085913313085100289)
      ·
        refine ⟨15536622814434984813825217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20715497085913313085100289 15536622814434984813825217)
        ·
          refine ⟨11652467110826238610368913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15536622814434984813825217 11652467110826238610368913)
          ·
            refine ⟨8739350333119678957776685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11652467110826238610368913 8739350333119678957776685)
            ·
              refine ⟨3277256374919879609166257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8739350333119678957776685 3277256374919879609166257)
              ·
                refine ⟨2457942281189909706874693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3277256374919879609166257 2457942281189909706874693)
                ·
                  refine ⟨460864177723108070039005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2457942281189909706874693 460864177723108070039005)
                  ·
                    rfl

theorem cell21_2019442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 3, 2, 4].length) (baseStart_2019442 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2019442 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2019442 prefixEnd_2019442 := by exact prefixLift 2019442
  have htrace : WordTrace (prefixWord ++ tailWord_2019442) baseStart_2019442 baseEnd_2019442 := by
    simpa [prefixWord, tailWord_2019442, baseEnd_2019442] using wordTrace_append hprefix tailTrace_2019442
  have hstable : (prefixWord ++ tailWord_2019442).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2019442).length < 2 ^ (prefixWord ++ tailWord_2019442).sum := by decide
  have hdescent : baseEnd_2019442 < baseStart_2019442 := by decide
  rcases family_descends (prefixWord ++ tailWord_2019442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2019515 : List Nat := [1, 1, 1, 1, 1, 2, 8, 6]
def baseStart_2019515 : Nat := 118140960795 + 2019515 * 2 ^ 59
def prefixEnd_2019515 : Nat := 4983230072969 + 3 ^ 40 * 2019515 * 2
def baseEnd_2019515 : Nat := 153626945772558721774063

theorem tailTrace_2019515 : CollatzResearch.WordTrace tailWord_2019515 prefixEnd_2019515 153626945772558721774063 := by
  unfold tailWord_2019515
  simp only [CollatzResearch.WordTrace]
  refine ⟨73657763278649535547763999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49105175519099690365175999 73657763278649535547763999)
  ·
    refine ⟨110486644917974303321645999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73657763278649535547763999 110486644917974303321645999)
    ·
      refine ⟨165729967376961454982468999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110486644917974303321645999 165729967376961454982468999)
      ·
        refine ⟨248594951065442182473703499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165729967376961454982468999 248594951065442182473703499)
        ·
          refine ⟨372892426598163273710555249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248594951065442182473703499 372892426598163273710555249)
          ·
            refine ⟨279669319948622455282916437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 372892426598163273710555249 279669319948622455282916437)
            ·
              refine ⟨3277374843147919397846677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 279669319948622455282916437 3277374843147919397846677)
              ·
                refine ⟨153626945772558721774063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3277374843147919397846677 153626945772558721774063)
                ·
                  rfl

theorem cell21_2019515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 8, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 8, 6].length) (baseStart_2019515 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2019515 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2019515 prefixEnd_2019515 := by exact prefixLift 2019515
  have htrace : WordTrace (prefixWord ++ tailWord_2019515) baseStart_2019515 baseEnd_2019515 := by
    simpa [prefixWord, tailWord_2019515, baseEnd_2019515] using wordTrace_append hprefix tailTrace_2019515
  have hstable : (prefixWord ++ tailWord_2019515).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2019515).length < 2 ^ (prefixWord ++ tailWord_2019515).sum := by decide
  have hdescent : baseEnd_2019515 < baseStart_2019515 := by decide
  rcases family_descends (prefixWord ++ tailWord_2019515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2019555 : List Nat := [1, 1, 1, 8, 2, 1, 2, 2, 3]
def baseStart_2019555 : Nat := 118140960795 + 2019555 * 2 ^ 59
def prefixEnd_2019555 : Nat := 4983230072969 + 3 ^ 40 * 2019555 * 2
def baseEnd_2019555 : Nat := 460889965862644984655441

theorem tailTrace_2019555 : CollatzResearch.WordTrace tailWord_2019555 prefixEnd_2019555 460889965862644984655441 := by
  unfold tailWord_2019555
  simp only [CollatzResearch.WordTrace]
  refine ⟨73659222198504622379220119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49106148132336414919480079 73659222198504622379220119)
  ·
    refine ⟨110488833297756933568830179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73659222198504622379220119 110488833297756933568830179)
    ·
      refine ⟨165733249946635400353245269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110488833297756933568830179 165733249946635400353245269)
      ·
        refine ⟨1942186522812133597889593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 165733249946635400353245269 1942186522812133597889593)
        ·
          refine ⟨1456639892109100198417195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1942186522812133597889593 1456639892109100198417195)
          ·
            refine ⟨2184959838163650297625793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1456639892109100198417195 2184959838163650297625793)
            ·
              refine ⟨1638719878622737723219345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2184959838163650297625793 1638719878622737723219345)
              ·
                refine ⟨1229039908967053292414509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1638719878622737723219345 1229039908967053292414509)
                ·
                  refine ⟨460889965862644984655441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1229039908967053292414509 460889965862644984655441)
                  ·
                    rfl

theorem cell21_2019555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 2, 2, 3].length) (baseStart_2019555 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2019555 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2019555 prefixEnd_2019555 := by exact prefixLift 2019555
  have htrace : WordTrace (prefixWord ++ tailWord_2019555) baseStart_2019555 baseEnd_2019555 := by
    simpa [prefixWord, tailWord_2019555, baseEnd_2019555] using wordTrace_append hprefix tailTrace_2019555
  have hstable : (prefixWord ++ tailWord_2019555).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2019555).length < 2 ^ (prefixWord ++ tailWord_2019555).sum := by decide
  have hdescent : baseEnd_2019555 < baseStart_2019555 := by decide
  rcases family_descends (prefixWord ++ tailWord_2019555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2019563 : List Nat := [1, 1, 1, 1, 2, 5, 3, 4, 3]
def baseStart_2019563 : Nat := 118140960795 + 2019563 * 2 ^ 59
def prefixEnd_2019563 : Nat := 4983230072969 + 3 ^ 40 * 2019563 * 2
def baseEnd_2019563 : Nat := 460891791571638748522091

theorem tailTrace_2019563 : CollatzResearch.WordTrace tailWord_2019563 prefixEnd_2019563 460891791571638748522091 := by
  unfold tailWord_2019563
  simp only [CollatzResearch.WordTrace]
  refine ⟨73659513982475639745511343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49106342654983759830340895 73659513982475639745511343)
  ·
    refine ⟨110489270973713459618267015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73659513982475639745511343 110489270973713459618267015)
    ·
      refine ⟨165733906460570189427400523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110489270973713459618267015 165733906460570189427400523)
      ·
        refine ⟨248600859690855284141100785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165733906460570189427400523 248600859690855284141100785)
        ·
          refine ⟨186450644768141463105825589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 248600859690855284141100785 186450644768141463105825589)
          ·
            refine ⟨17479747947013262166171149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 186450644768141463105825589 17479747947013262166171149)
            ·
              refine ⟨6554905480129973312314181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17479747947013262166171149 6554905480129973312314181)
              ·
                refine ⟨1229044777524369996058909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6554905480129973312314181 1229044777524369996058909)
                ·
                  refine ⟨460891791571638748522091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1229044777524369996058909 460891791571638748522091)
                  ·
                    rfl

theorem cell21_2019563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 3, 4, 3].length) (baseStart_2019563 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2019563 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2019563 prefixEnd_2019563 := by exact prefixLift 2019563
  have htrace : WordTrace (prefixWord ++ tailWord_2019563) baseStart_2019563 baseEnd_2019563 := by
    simpa [prefixWord, tailWord_2019563, baseEnd_2019563] using wordTrace_append hprefix tailTrace_2019563
  have hstable : (prefixWord ++ tailWord_2019563).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2019563).length < 2 ^ (prefixWord ++ tailWord_2019563).sum := by decide
  have hdescent : baseEnd_2019563 < baseStart_2019563 := by decide
  rcases family_descends (prefixWord ++ tailWord_2019563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2019687 : List Nat := [1, 1, 5, 1, 3, 3, 2, 1, 4]
def baseStart_2019687 : Nat := 118140960795 + 2019687 * 2 ^ 59
def prefixEnd_2019687 : Nat := 4983230072969 + 3 ^ 40 * 2019687 * 2
def baseEnd_2019687 : Nat := 460920090061042088455171

theorem tailTrace_2019687 : CollatzResearch.WordTrace tailWord_2019687 prefixEnd_2019687 460920090061042088455171 := by
  unfold tailWord_2019687
  simp only [CollatzResearch.WordTrace]
  refine ⟨73664036634026408923025315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49109357756017605948683543 73664036634026408923025315)
  ·
    refine ⟨110496054951039613384537973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73664036634026408923025315 110496054951039613384537973)
    ·
      refine ⟨10359005151659963754800435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 110496054951039613384537973 10359005151659963754800435)
      ·
        refine ⟨15538507727489945632200653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10359005151659963754800435 15538507727489945632200653)
        ·
          refine ⟨5826940397808729612075245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15538507727489945632200653 5826940397808729612075245)
          ·
            refine ⟨2185102649178273604528217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5826940397808729612075245 2185102649178273604528217)
            ·
              refine ⟨1638826986883705203396163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2185102649178273604528217 1638826986883705203396163)
              ·
                refine ⟨2458240480325557805094245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1638826986883705203396163 2458240480325557805094245)
                ·
                  refine ⟨460920090061042088455171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2458240480325557805094245 460920090061042088455171)
                  ·
                    rfl

theorem cell21_2019687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 2, 1, 4].length) (baseStart_2019687 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2019687 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2019687 prefixEnd_2019687 := by exact prefixLift 2019687
  have htrace : WordTrace (prefixWord ++ tailWord_2019687) baseStart_2019687 baseEnd_2019687 := by
    simpa [prefixWord, tailWord_2019687, baseEnd_2019687] using wordTrace_append hprefix tailTrace_2019687
  have hstable : (prefixWord ++ tailWord_2019687).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2019687).length < 2 ^ (prefixWord ++ tailWord_2019687).sum := by decide
  have hdescent : baseEnd_2019687 < baseStart_2019687 := by decide
  rcases family_descends (prefixWord ++ tailWord_2019687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2019780 : List Nat := [2, 3, 3, 2, 3, 1, 1, 2, 4]
def baseStart_2019780 : Nat := 118140960795 + 2019780 * 2 ^ 59
def prefixEnd_2019780 : Nat := 4983230072969 + 3 ^ 40 * 2019780 * 2
def baseEnd_2019780 : Nat := 460941313928094593404981

theorem tailTrace_2019780 : CollatzResearch.WordTrace tailWord_2019780 prefixEnd_2019780 460941313928094593404981 := by
  unfold tailWord_2019780
  simp only [CollatzResearch.WordTrace]
  refine ⟨36833714311344742903080397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49111619081792990537440529 36833714311344742903080397)
  ·
    refine ⟨13812642866754278588655149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36833714311344742903080397 13812642866754278588655149)
    ·
      refine ⟨5179741075032854470745681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13812642866754278588655149 5179741075032854470745681)
      ·
        refine ⟨3884805806274640853059261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5179741075032854470745681 3884805806274640853059261)
        ·
          refine ⟨1456802177352990319897223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3884805806274640853059261 1456802177352990319897223)
          ·
            refine ⟨2185203266029485479845835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1456802177352990319897223 2185203266029485479845835)
            ·
              refine ⟨3277804899044228219768753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2185203266029485479845835 3277804899044228219768753)
              ·
                refine ⟨2458353674283171164826565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3277804899044228219768753 2458353674283171164826565)
                ·
                  refine ⟨460941313928094593404981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2458353674283171164826565 460941313928094593404981)
                  ·
                    rfl

theorem cell21_2019780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 1, 2, 4].length) (baseStart_2019780 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2019780 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2019780 prefixEnd_2019780 := by exact prefixLift 2019780
  have htrace : WordTrace (prefixWord ++ tailWord_2019780) baseStart_2019780 baseEnd_2019780 := by
    simpa [prefixWord, tailWord_2019780, baseEnd_2019780] using wordTrace_append hprefix tailTrace_2019780
  have hstable : (prefixWord ++ tailWord_2019780).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2019780).length < 2 ^ (prefixWord ++ tailWord_2019780).sum := by decide
  have hdescent : baseEnd_2019780 < baseStart_2019780 := by decide
  rcases family_descends (prefixWord ++ tailWord_2019780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2019833 : List Nat := [1, 2, 1, 3, 1, 2, 2, 2, 7]
def baseStart_2019833 : Nat := 118140960795 + 2019833 * 2 ^ 59
def prefixEnd_2019833 : Nat := 4983230072969 + 3 ^ 40 * 2019833 * 2
def baseEnd_2019833 : Nat := 460953409250178279021539

theorem tailTrace_2019833 : CollatzResearch.WordTrace tailWord_2019833 prefixEnd_2019833 460953409250178279021539 := by
  unfold tailWord_2019833
  simp only [CollatzResearch.WordTrace]
  refine ⟨73669361691497475857840153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49112907794331650571893435 73669361691497475857840153)
  ·
    refine ⟨55252021268623106893380115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73669361691497475857840153 55252021268623106893380115)
    ·
      refine ⟨82878031902934660340070173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55252021268623106893380115 82878031902934660340070173)
      ·
        refine ⟨31079261963600497627526315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82878031902934660340070173 31079261963600497627526315)
        ·
          refine ⟨46618892945400746441289473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31079261963600497627526315 46618892945400746441289473)
          ·
            refine ⟨34964169709050559830967105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46618892945400746441289473 34964169709050559830967105)
            ·
              refine ⟨26223127281787919873225329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34964169709050559830967105 26223127281787919873225329)
              ·
                refine ⟨19667345461340939904918997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26223127281787919873225329 19667345461340939904918997)
                ·
                  refine ⟨460953409250178279021539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19667345461340939904918997 460953409250178279021539)
                  ·
                    rfl

theorem cell21_2019833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 2, 7].length) (baseStart_2019833 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2019833 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2019833 prefixEnd_2019833 := by exact prefixLift 2019833
  have htrace : WordTrace (prefixWord ++ tailWord_2019833) baseStart_2019833 baseEnd_2019833 := by
    simpa [prefixWord, tailWord_2019833, baseEnd_2019833] using wordTrace_append hprefix tailTrace_2019833
  have hstable : (prefixWord ++ tailWord_2019833).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2019833).length < 2 ^ (prefixWord ++ tailWord_2019833).sum := by decide
  have hdescent : baseEnd_2019833 < baseStart_2019833 := by decide
  rcases family_descends (prefixWord ++ tailWord_2019833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2019842 : List Nat := [3, 4, 1, 2, 2, 1, 3, 2, 3]
def baseStart_2019842 : Nat := 118140960795 + 2019842 * 2 ^ 59
def prefixEnd_2019842 : Nat := 4983230072969 + 3 ^ 40 * 2019842 * 2
def baseEnd_2019842 : Nat := 460955463172796263371521

theorem tailTrace_2019842 : CollatzResearch.WordTrace tailWord_2019842 prefixEnd_2019842 460955463172796263371521 := by
  unfold tailWord_2019842
  simp only [CollatzResearch.WordTrace]
  refine ⟨18417422487116217598729445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49113126632309913596611853 18417422487116217598729445)
  ·
    refine ⟨3453266716334290799761771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18417422487116217598729445 3453266716334290799761771)
    ·
      refine ⟨5179900074501436199642657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3453266716334290799761771 5179900074501436199642657)
      ·
        refine ⟨3884925055876077149731993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5179900074501436199642657 3884925055876077149731993)
        ·
          refine ⟨2913693791907057862298995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3884925055876077149731993 2913693791907057862298995)
          ·
            refine ⟨4370540687860586793448493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2913693791907057862298995 4370540687860586793448493)
            ·
              refine ⟨1638952757947720047543185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4370540687860586793448493 1638952757947720047543185)
              ·
                refine ⟨1229214568460790035657389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1638952757947720047543185 1229214568460790035657389)
                ·
                  refine ⟨460955463172796263371521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1229214568460790035657389 460955463172796263371521)
                  ·
                    rfl

theorem cell21_2019842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 3, 2, 3].length) (baseStart_2019842 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2019842 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2019842 prefixEnd_2019842 := by exact prefixLift 2019842
  have htrace : WordTrace (prefixWord ++ tailWord_2019842) baseStart_2019842 baseEnd_2019842 := by
    simpa [prefixWord, tailWord_2019842, baseEnd_2019842] using wordTrace_append hprefix tailTrace_2019842
  have hstable : (prefixWord ++ tailWord_2019842).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2019842).length < 2 ^ (prefixWord ++ tailWord_2019842).sum := by decide
  have hdescent : baseEnd_2019842 < baseStart_2019842 := by decide
  rcases family_descends (prefixWord ++ tailWord_2019842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2019853 : List Nat := [1, 7, 1, 1, 1, 1, 1, 8]
def baseStart_2019853 : Nat := 118140960795 + 2019853 * 2 ^ 59
def prefixEnd_2019853 : Nat := 4983230072969 + 3 ^ 40 * 2019853 * 2
def baseEnd_2019853 : Nat := 153652657840887562896055

theorem tailTrace_2019853 : CollatzResearch.WordTrace tailWord_2019853 prefixEnd_2019853 153652657840887562896055 := by
  unfold tailWord_2019853
  simp only [CollatzResearch.WordTrace]
  refine ⟨73670091151425019273568213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49113394100950012849045475 73670091151425019273568213)
  ·
    refine ⟨1726642761361523889224255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 73670091151425019273568213 1726642761361523889224255)
    ·
      refine ⟨2589964142042285833836383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1726642761361523889224255 2589964142042285833836383)
      ·
        refine ⟨3884946213063428750754575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2589964142042285833836383 3884946213063428750754575)
        ·
          refine ⟨5827419319595143126131863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3884946213063428750754575 5827419319595143126131863)
          ·
            refine ⟨8741128979392714689197795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5827419319595143126131863 8741128979392714689197795)
            ·
              refine ⟨13111693469089072033796693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8741128979392714689197795 13111693469089072033796693)
              ·
                refine ⟨153652657840887562896055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13111693469089072033796693 153652657840887562896055)
                ·
                  rfl

theorem cell21_2019853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 8].length) (baseStart_2019853 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2019853 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2019853 prefixEnd_2019853 := by exact prefixLift 2019853
  have htrace : WordTrace (prefixWord ++ tailWord_2019853) baseStart_2019853 baseEnd_2019853 := by
    simpa [prefixWord, tailWord_2019853, baseEnd_2019853] using wordTrace_append hprefix tailTrace_2019853
  have hstable : (prefixWord ++ tailWord_2019853).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2019853).length < 2 ^ (prefixWord ++ tailWord_2019853).sum := by decide
  have hdescent : baseEnd_2019853 < baseStart_2019853 := by decide
  rcases family_descends (prefixWord ++ tailWord_2019853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2019901 : List Nat := [1, 4, 1, 3, 2, 3, 2, 2, 3]
def baseStart_2019901 : Nat := 118140960795 + 2019901 * 2 ^ 59
def prefixEnd_2019901 : Nat := 4983230072969 + 3 ^ 40 * 2019901 * 2
def baseEnd_2019901 : Nat := 460968927776625271888067

theorem tailTrace_2019901 : CollatzResearch.WordTrace tailWord_2019901 prefixEnd_2019901 460968927776625271888067 := by
  unfold tailWord_2019901
  simp only [CollatzResearch.WordTrace]
  refine ⟨73671841855251123471315557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49114561236834082314210371 73671841855251123471315557)
  ·
    refine ⟨13813470347859585650871667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73671841855251123471315557 13813470347859585650871667)
    ·
      refine ⟨20720205521789378476307501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13813470347859585650871667 20720205521789378476307501)
      ·
        refine ⟨7770077070671016928615313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20720205521789378476307501 7770077070671016928615313)
        ·
          refine ⟨5827557803003262696461485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7770077070671016928615313 5827557803003262696461485)
          ·
            refine ⟨2185334176126223511173057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5827557803003262696461485 2185334176126223511173057)
            ·
              refine ⟨1639000632094667633379793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2185334176126223511173057 1639000632094667633379793)
              ·
                refine ⟨1229250474071000725034845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1639000632094667633379793 1229250474071000725034845)
                ·
                  refine ⟨460968927776625271888067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1229250474071000725034845 460968927776625271888067)
                  ·
                    rfl

theorem cell21_2019901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 2, 2, 3].length) (baseStart_2019901 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2019901 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2019901 prefixEnd_2019901 := by exact prefixLift 2019901
  have htrace : WordTrace (prefixWord ++ tailWord_2019901) baseStart_2019901 baseEnd_2019901 := by
    simpa [prefixWord, tailWord_2019901, baseEnd_2019901] using wordTrace_append hprefix tailTrace_2019901
  have hstable : (prefixWord ++ tailWord_2019901).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2019901).length < 2 ^ (prefixWord ++ tailWord_2019901).sum := by decide
  have hdescent : baseEnd_2019901 < baseStart_2019901 := by decide
  rcases family_descends (prefixWord ++ tailWord_2019901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2019940 : List Nat := [2, 3, 1, 1, 2, 2, 2, 2, 6]
def baseStart_2019940 : Nat := 118140960795 + 2019940 * 2 ^ 59
def prefixEnd_2019940 : Nat := 4983230072969 + 3 ^ 40 * 2019940 * 2
def baseEnd_2019940 : Nat := 460977828107969870737987

theorem tailTrace_2019940 : CollatzResearch.WordTrace tailWord_2019940 prefixEnd_2019940 460977828107969870737987 := by
  unfold tailWord_2019940
  simp only [CollatzResearch.WordTrace]
  refine ⟨36836632151054916565992637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49115509534739888754656849 36836632151054916565992637)
  ·
    refine ⟨13813737056645593712247239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36836632151054916565992637 13813737056645593712247239)
    ·
      refine ⟨20720605584968390568370859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13813737056645593712247239 20720605584968390568370859)
      ·
        refine ⟨31080908377452585852556289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20720605584968390568370859 31080908377452585852556289)
        ·
          refine ⟨23310681283089439389417217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31080908377452585852556289 23310681283089439389417217)
          ·
            refine ⟨17483010962317079542062913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23310681283089439389417217 17483010962317079542062913)
            ·
              refine ⟨13112258221737809656547185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17483010962317079542062913 13112258221737809656547185)
              ·
                refine ⟨9834193666303357242410389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13112258221737809656547185 9834193666303357242410389)
                ·
                  refine ⟨460977828107969870737987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9834193666303357242410389 460977828107969870737987)
                  ·
                    rfl

theorem cell21_2019940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 2, 6].length) (baseStart_2019940 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2019940 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2019940 prefixEnd_2019940 := by exact prefixLift 2019940
  have htrace : WordTrace (prefixWord ++ tailWord_2019940) baseStart_2019940 baseEnd_2019940 := by
    simpa [prefixWord, tailWord_2019940, baseEnd_2019940] using wordTrace_append hprefix tailTrace_2019940
  have hstable : (prefixWord ++ tailWord_2019940).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2019940).length < 2 ^ (prefixWord ++ tailWord_2019940).sum := by decide
  have hdescent : baseEnd_2019940 < baseStart_2019940 := by decide
  rcases family_descends (prefixWord ++ tailWord_2019940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2019988 : List Nat := [2, 4, 2, 2, 1, 2, 1, 7]
def baseStart_2019988 : Nat := 118140960795 + 2019988 * 2 ^ 59
def prefixEnd_2019988 : Nat := 4983230072969 + 3 ^ 40 * 2019988 * 2
def baseEnd_2019988 : Nat := 153662927453977484645963

theorem tailTrace_2019988 : CollatzResearch.WordTrace tailWord_2019988 prefixEnd_2019988 153662927453977484645963 := by
  unfold tailWord_2019988
  simp only [CollatzResearch.WordTrace]
  refine ⟨36837507502967968664866309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49116676670623958219821745 36837507502967968664866309)
  ·
    refine ⟨6907032656806494124662433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36837507502967968664866309 6907032656806494124662433)
    ·
      refine ⟨5180274492604870593496825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6907032656806494124662433 5180274492604870593496825)
      ·
        refine ⟨3885205869453652945122619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5180274492604870593496825 3885205869453652945122619)
        ·
          refine ⟨5827808804180479417683929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3885205869453652945122619 5827808804180479417683929)
          ·
            refine ⟨4370856603135359563262947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5827808804180479417683929 4370856603135359563262947)
            ·
              refine ⟨6556284904703039344894421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4370856603135359563262947 6556284904703039344894421)
              ·
                refine ⟨153662927453977484645963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6556284904703039344894421 153662927453977484645963)
                ·
                  rfl

theorem cell21_2019988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 1, 7].length) (baseStart_2019988 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2019988 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2019988 prefixEnd_2019988 := by exact prefixLift 2019988
  have htrace : WordTrace (prefixWord ++ tailWord_2019988) baseStart_2019988 baseEnd_2019988 := by
    simpa [prefixWord, tailWord_2019988, baseEnd_2019988] using wordTrace_append hprefix tailTrace_2019988
  have hstable : (prefixWord ++ tailWord_2019988).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2019988).length < 2 ^ (prefixWord ++ tailWord_2019988).sum := by decide
  have hdescent : baseEnd_2019988 < baseStart_2019988 := by decide
  rcases family_descends (prefixWord ++ tailWord_2019988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2019994 : List Nat := [3, 1, 1, 6, 2, 1, 1, 3, 3]
def baseStart_2019994 : Nat := 118140960795 + 2019994 * 2 ^ 59
def prefixEnd_2019994 : Nat := 4983230072969 + 3 ^ 40 * 2019994 * 2
def baseEnd_2019994 : Nat := 460990151643677776837877

theorem tailTrace_2019994 : CollatzResearch.WordTrace tailWord_2019994 prefixEnd_2019994 460990151643677776837877 := by
  unfold tailWord_2019994
  simp only [CollatzResearch.WordTrace]
  refine ⟨18418808460978550088612759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49116822562609466902967357 18418808460978550088612759)
  ·
    refine ⟨27628212691467825132919139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18418808460978550088612759 27628212691467825132919139)
    ·
      refine ⟨41442319037201737699378709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27628212691467825132919139 41442319037201737699378709)
      ·
        refine ⟨1942608704868831454658377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 41442319037201737699378709 1942608704868831454658377)
        ·
          refine ⟨1456956528651623590993783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1942608704868831454658377 1456956528651623590993783)
          ·
            refine ⟨2185434792977435386490675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1456956528651623590993783 2185434792977435386490675)
            ·
              refine ⟨3278152189466153079736013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2185434792977435386490675 3278152189466153079736013)
              ·
                refine ⟨1229307071049807404901005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3278152189466153079736013 1229307071049807404901005)
                ·
                  refine ⟨460990151643677776837877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1229307071049807404901005 460990151643677776837877)
                  ·
                    rfl

theorem cell21_2019994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 1, 3, 3].length) (baseStart_2019994 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2019994 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2019994 prefixEnd_2019994 := by exact prefixLift 2019994
  have htrace : WordTrace (prefixWord ++ tailWord_2019994) baseStart_2019994 baseEnd_2019994 := by
    simpa [prefixWord, tailWord_2019994, baseEnd_2019994] using wordTrace_append hprefix tailTrace_2019994
  have hstable : (prefixWord ++ tailWord_2019994).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2019994).length < 2 ^ (prefixWord ++ tailWord_2019994).sum := by decide
  have hdescent : baseEnd_2019994 < baseStart_2019994 := by decide
  rcases family_descends (prefixWord ++ tailWord_2019994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2020016 : List Nat := [2, 1, 1, 1, 2, 1, 3, 6, 4]
def baseStart_2020016 : Nat := 118140960795 + 2020016 * 2 ^ 59
def prefixEnd_2020016 : Nat := 4983230072969 + 3 ^ 40 * 2020016 * 2
def baseEnd_2020016 : Nat := 460995172343410627471165

theorem tailTrace_2020016 : CollatzResearch.WordTrace tailWord_2020016 prefixEnd_2020016 460995172343410627471165 := by
  unfold tailWord_2020016
  simp only [CollatzResearch.WordTrace]
  refine ⟨36838018124917249055875951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49117357499889665407834601 36838018124917249055875951)
  ·
    refine ⟨55257027187375873583813927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36838018124917249055875951 55257027187375873583813927)
    ·
      refine ⟨82885540781063810375720891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55257027187375873583813927 82885540781063810375720891)
      ·
        refine ⟨124328311171595715563581337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82885540781063810375720891 124328311171595715563581337)
        ·
          refine ⟨93246233378696786672686003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124328311171595715563581337 93246233378696786672686003)
          ·
            refine ⟨139869350068045180009029005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93246233378696786672686003 139869350068045180009029005)
            ·
              refine ⟨52451006275516942503385877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 139869350068045180009029005 52451006275516942503385877)
              ·
                refine ⟨2458640919164856679846213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 52451006275516942503385877 2458640919164856679846213)
                ·
                  refine ⟨460995172343410627471165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2458640919164856679846213 460995172343410627471165)
                  ·
                    rfl

theorem cell21_2020016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 6, 4].length) (baseStart_2020016 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2020016 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2020016 prefixEnd_2020016 := by exact prefixLift 2020016
  have htrace : WordTrace (prefixWord ++ tailWord_2020016) baseStart_2020016 baseEnd_2020016 := by
    simpa [prefixWord, tailWord_2020016, baseEnd_2020016] using wordTrace_append hprefix tailTrace_2020016
  have hstable : (prefixWord ++ tailWord_2020016).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2020016).length < 2 ^ (prefixWord ++ tailWord_2020016).sum := by decide
  have hdescent : baseEnd_2020016 < baseStart_2020016 := by decide
  rcases family_descends (prefixWord ++ tailWord_2020016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2020157 : List Nat := [1, 4, 1, 4, 2, 2, 2, 5]
def baseStart_2020157 : Nat := 118140960795 + 2020157 * 2 ^ 59
def prefixEnd_2020157 : Nat := 4983230072969 + 3 ^ 40 * 2020157 * 2
def baseEnd_2020157 : Nat := 153675783488141905206959

theorem tailTrace_2020157 : CollatzResearch.WordTrace tailWord_2020157 prefixEnd_2020157 153675783488141905206959 := by
  unfold tailWord_2020157
  simp only [CollatzResearch.WordTrace]
  refine ⟨73681178942323679192634725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49120785961549119461756483 73681178942323679192634725)
  ·
    refine ⟨13815221051685689848619011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73681178942323679192634725 13815221051685689848619011)
    ·
      refine ⟨20722831577528534772928517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13815221051685689848619011 20722831577528534772928517)
      ·
        refine ⟨3885530920786600269924097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20722831577528534772928517 3885530920786600269924097)
        ·
          refine ⟨2914148190589950202443073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3885530920786600269924097 2914148190589950202443073)
          ·
            refine ⟨2185611142942462651832305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2914148190589950202443073 2185611142942462651832305)
            ·
              refine ⟨1639208357206846988874229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2185611142942462651832305 1639208357206846988874229)
              ·
                refine ⟨153675783488141905206959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1639208357206846988874229 153675783488141905206959)
                ·
                  rfl

theorem cell21_2020157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 2, 5].length) (baseStart_2020157 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2020157 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2020157 prefixEnd_2020157 := by exact prefixLift 2020157
  have htrace : WordTrace (prefixWord ++ tailWord_2020157) baseStart_2020157 baseEnd_2020157 := by
    simpa [prefixWord, tailWord_2020157, baseEnd_2020157] using wordTrace_append hprefix tailTrace_2020157
  have hstable : (prefixWord ++ tailWord_2020157).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2020157).length < 2 ^ (prefixWord ++ tailWord_2020157).sum := by decide
  have hdescent : baseEnd_2020157 < baseStart_2020157 := by decide
  rcases family_descends (prefixWord ++ tailWord_2020157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2020199 : List Nat := [1, 1, 5, 1, 2, 3, 2, 6]
def baseStart_2020199 : Nat := 118140960795 + 2020199 * 2 ^ 59
def prefixEnd_2020199 : Nat := 4983230072969 + 3 ^ 40 * 2020199 * 2
def baseEnd_2020199 : Nat := 153678978478880991973597

theorem tailTrace_2020199 : CollatzResearch.WordTrace tailWord_2020199 prefixEnd_2020199 153678978478880991973597 := by
  unfold tailWord_2020199
  simp only [CollatzResearch.WordTrace]
  refine ⟨73682710808171520365663651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49121807205447680243775767 73682710808171520365663651)
  ·
    refine ⟨110524066212257280548495477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73682710808171520365663651 110524066212257280548495477)
    ·
      refine ⟨10361631207399120051421451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 110524066212257280548495477 10361631207399120051421451)
      ·
        refine ⟨15542446811098680077132177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10361631207399120051421451 15542446811098680077132177)
        ·
          refine ⟨11656835108324010057849133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15542446811098680077132177 11656835108324010057849133)
          ·
            refine ⟨4371313165621503771693425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11656835108324010057849133 4371313165621503771693425)
            ·
              refine ⟨3278484874216127828770069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4371313165621503771693425 3278484874216127828770069)
              ·
                refine ⟨153678978478880991973597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3278484874216127828770069 153678978478880991973597)
                ·
                  rfl

theorem cell21_2020199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 2, 6].length) (baseStart_2020199 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2020199 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2020199 prefixEnd_2020199 := by exact prefixLift 2020199
  have htrace : WordTrace (prefixWord ++ tailWord_2020199) baseStart_2020199 baseEnd_2020199 := by
    simpa [prefixWord, tailWord_2020199, baseEnd_2020199] using wordTrace_append hprefix tailTrace_2020199
  have hstable : (prefixWord ++ tailWord_2020199).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2020199).length < 2 ^ (prefixWord ++ tailWord_2020199).sum := by decide
  have hdescent : baseEnd_2020199 < baseStart_2020199 := by decide
  rcases family_descends (prefixWord ++ tailWord_2020199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2020292 : List Nat := [2, 3, 3, 3, 1, 1, 8]
def baseStart_2020292 : Nat := 118140960795 + 2020292 * 2 ^ 59
def prefixEnd_2020292 : Nat := 4983230072969 + 3 ^ 40 * 2020292 * 2
def baseEnd_2020292 : Nat := 51228684367077275652289

theorem tailTrace_2020292 : CollatzResearch.WordTrace tailWord_2020292 prefixEnd_2020292 51228684367077275652289 := by
  unfold tailWord_2020292
  simp only [CollatzResearch.WordTrace]
  refine ⟨36843051398417298624399565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49124068531223064832532753 36843051398417298624399565)
  ·
    refine ⟨13816144274406486984149837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36843051398417298624399565 13816144274406486984149837)
    ·
      refine ⟨5181054102902432619056189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13816144274406486984149837 5181054102902432619056189)
      ·
        refine ⟨1942895288588412232146071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5181054102902432619056189 1942895288588412232146071)
        ·
          refine ⟨2914342932882618348219107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1942895288588412232146071 2914342932882618348219107)
          ·
            refine ⟨4371514399323927522328661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2914342932882618348219107 4371514399323927522328661)
            ·
              refine ⟨51228684367077275652289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4371514399323927522328661 51228684367077275652289)
              ·
                rfl

theorem cell21_2020292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 8].length) (baseStart_2020292 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2020292 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2020292 prefixEnd_2020292 := by exact prefixLift 2020292
  have htrace : WordTrace (prefixWord ++ tailWord_2020292) baseStart_2020292 baseEnd_2020292 := by
    simpa [prefixWord, tailWord_2020292, baseEnd_2020292] using wordTrace_append hprefix tailTrace_2020292
  have hstable : (prefixWord ++ tailWord_2020292).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2020292).length < 2 ^ (prefixWord ++ tailWord_2020292).sum := by decide
  have hdescent : baseEnd_2020292 < baseStart_2020292 := by decide
  rcases family_descends (prefixWord ++ tailWord_2020292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2020306 : List Nat := [3, 2, 2, 3, 1, 1, 1, 3, 5]
def baseStart_2020306 : Nat := 118140960795 + 2020306 * 2 ^ 59
def prefixEnd_2020306 : Nat := 4983230072969 + 3 ^ 40 * 2020306 * 2
def baseEnd_2020306 : Nat := 461061354294434567637239

theorem tailTrace_2020306 : CollatzResearch.WordTrace tailWord_2020306 prefixEnd_2020306 461061354294434567637239 := by
  unfold tailWord_2020306
  simp only [CollatzResearch.WordTrace]
  refine ⟨18421653354695969409952193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49124408945855918426539181 18421653354695969409952193)
  ·
    refine ⟨13816240016021977057464145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18421653354695969409952193 13816240016021977057464145)
    ·
      refine ⟨10362180012016482793098109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13816240016021977057464145 10362180012016482793098109)
      ·
        refine ⟨3885817504506181047411791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10362180012016482793098109 3885817504506181047411791)
        ·
          refine ⟨5828726256759271571117687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3885817504506181047411791 5828726256759271571117687)
          ·
            refine ⟨8743089385138907356676531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5828726256759271571117687 8743089385138907356676531)
            ·
              refine ⟨13114634077708361035014797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8743089385138907356676531 13114634077708361035014797)
              ·
                refine ⟨4917987779140635388130549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13114634077708361035014797 4917987779140635388130549)
                ·
                  refine ⟨461061354294434567637239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4917987779140635388130549 461061354294434567637239)
                  ·
                    rfl

theorem cell21_2020306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 3, 5].length) (baseStart_2020306 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2020306 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2020306 prefixEnd_2020306 := by exact prefixLift 2020306
  have htrace : WordTrace (prefixWord ++ tailWord_2020306) baseStart_2020306 baseEnd_2020306 := by
    simpa [prefixWord, tailWord_2020306, baseEnd_2020306] using wordTrace_append hprefix tailTrace_2020306
  have hstable : (prefixWord ++ tailWord_2020306).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2020306).length < 2 ^ (prefixWord ++ tailWord_2020306).sum := by decide
  have hdescent : baseEnd_2020306 < baseStart_2020306 := by decide
  rcases family_descends (prefixWord ++ tailWord_2020306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2020413 : List Nat := [1, 4, 1, 3, 1, 3, 2, 2, 4]
def baseStart_2020413 : Nat := 118140960795 + 2020413 * 2 ^ 59
def prefixEnd_2020413 : Nat := 4983230072969 + 3 ^ 40 * 2020413 * 2
def baseEnd_2020413 : Nat := 461085773152226159353687

theorem tailTrace_2020413 : CollatzResearch.WordTrace tailWord_2020413 prefixEnd_2020413 461085773152226159353687 := by
  unfold tailWord_2020413
  simp only [CollatzResearch.WordTrace]
  refine ⟨73690516029396234913953893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49127010686264156609302595 73690516029396234913953893)
  ·
    refine ⟨13816971755511794046366355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73690516029396234913953893 13816971755511794046366355)
    ·
      refine ⟨20725457633267691069549533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13816971755511794046366355 20725457633267691069549533)
      ·
        refine ⟨7772046612475384151081075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20725457633267691069549533 7772046612475384151081075)
        ·
          refine ⟨11658069918713076226621613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7772046612475384151081075 11658069918713076226621613)
          ·
            refine ⟨4371776219517403584983105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11658069918713076226621613 4371776219517403584983105)
            ·
              refine ⟨3278832164638052688737329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4371776219517403584983105 3278832164638052688737329)
              ·
                refine ⟨2459124123478539516552997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3278832164638052688737329 2459124123478539516552997)
                ·
                  refine ⟨461085773152226159353687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2459124123478539516552997 461085773152226159353687)
                  ·
                    rfl

theorem cell21_2020413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 2, 2, 4].length) (baseStart_2020413 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2020413 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2020413 prefixEnd_2020413 := by exact prefixLift 2020413
  have htrace : WordTrace (prefixWord ++ tailWord_2020413) baseStart_2020413 baseEnd_2020413 := by
    simpa [prefixWord, tailWord_2020413, baseEnd_2020413] using wordTrace_append hprefix tailTrace_2020413
  have hstable : (prefixWord ++ tailWord_2020413).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2020413).length < 2 ^ (prefixWord ++ tailWord_2020413).sum := by decide
  have hdescent : baseEnd_2020413 < baseStart_2020413 := by decide
  rcases family_descends (prefixWord ++ tailWord_2020413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2020472 : List Nat := [2, 1, 2, 1, 1, 1, 7, 2, 4]
def baseStart_2020472 : Nat := 118140960795 + 2020472 * 2 ^ 59
def prefixEnd_2020472 : Nat := 4983230072969 + 3 ^ 40 * 2020472 * 2
def baseEnd_2020472 : Nat := 461099237756055167870233

theorem tailTrace_2020472 : CollatzResearch.WordTrace tailWord_2020472 prefixEnd_2020472 461099237756055167870233 := by
  unfold tailWord_2020472
  simp only [CollatzResearch.WordTrace]
  refine ⟨36846333968091243995175835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49128445290788325326901113 36846333968091243995175835)
  ·
    refine ⟨55269500952136865992763753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36846333968091243995175835 55269500952136865992763753)
    ·
      refine ⟨41452125714102649494572815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55269500952136865992763753 41452125714102649494572815)
      ·
        refine ⟨62178188571153974241859223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41452125714102649494572815 62178188571153974241859223)
        ·
          refine ⟨93267282856730961362788835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62178188571153974241859223 93267282856730961362788835)
          ·
            refine ⟨139900924285096442044183253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93267282856730961362788835 139900924285096442044183253)
            ·
              refine ⟨3278927912931947860410545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 139900924285096442044183253 3278927912931947860410545)
              ·
                refine ⟨2459195934698960895307909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3278927912931947860410545 2459195934698960895307909)
                ·
                  refine ⟨461099237756055167870233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2459195934698960895307909 461099237756055167870233)
                  ·
                    rfl

theorem cell21_2020472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 7, 2, 4].length) (baseStart_2020472 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2020472 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2020472 prefixEnd_2020472 := by exact prefixLift 2020472
  have htrace : WordTrace (prefixWord ++ tailWord_2020472) baseStart_2020472 baseEnd_2020472 := by
    simpa [prefixWord, tailWord_2020472, baseEnd_2020472] using wordTrace_append hprefix tailTrace_2020472
  have hstable : (prefixWord ++ tailWord_2020472).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2020472).length < 2 ^ (prefixWord ++ tailWord_2020472).sum := by decide
  have hdescent : baseEnd_2020472 < baseStart_2020472 := by decide
  rcases family_descends (prefixWord ++ tailWord_2020472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2020489 : List Nat := [1, 2, 1, 1, 4, 4, 3, 1, 4]
def baseStart_2020489 : Nat := 118140960795 + 2020489 * 2 ^ 59
def prefixEnd_2020489 : Nat := 4983230072969 + 3 ^ 40 * 2020489 * 2
def baseEnd_2020489 : Nat := 461103117387666916086865

theorem tailTrace_2020489 : CollatzResearch.WordTrace tailWord_2020489 prefixEnd_2020489 461103117387666916086865 := by
  unfold tailWord_2020489
  simp only [CollatzResearch.WordTrace]
  refine ⟨73693287977120899893720521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49128858651413933262480347 73693287977120899893720521)
  ·
    refine ⟨55269965982840674920290391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73693287977120899893720521 55269965982840674920290391)
    ·
      refine ⟨82904948974261012380435587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55269965982840674920290391 82904948974261012380435587)
      ·
        refine ⟨124357423461391518570653381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82904948974261012380435587 124357423461391518570653381)
        ·
          refine ⟨23317016899010909731997509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 124357423461391518570653381 23317016899010909731997509)
          ·
            refine ⟨4371940668564545574749533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23317016899010909731997509 4371940668564545574749533)
            ·
              refine ⟨1639477750711704590531075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4371940668564545574749533 1639477750711704590531075)
              ·
                refine ⟨2459216626067556885796613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1639477750711704590531075 2459216626067556885796613)
                ·
                  refine ⟨461103117387666916086865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2459216626067556885796613 461103117387666916086865)
                  ·
                    rfl

theorem cell21_2020489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 3, 1, 4].length) (baseStart_2020489 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2020489 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2020489 prefixEnd_2020489 := by exact prefixLift 2020489
  have htrace : WordTrace (prefixWord ++ tailWord_2020489) baseStart_2020489 baseEnd_2020489 := by
    simpa [prefixWord, tailWord_2020489, baseEnd_2020489] using wordTrace_append hprefix tailTrace_2020489
  have hstable : (prefixWord ++ tailWord_2020489).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2020489).length < 2 ^ (prefixWord ++ tailWord_2020489).sum := by decide
  have hdescent : baseEnd_2020489 < baseStart_2020489 := by decide
  rcases family_descends (prefixWord ++ tailWord_2020489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2020503 : List Nat := [1, 1, 3, 3, 3, 1, 4, 5]
def baseStart_2020503 : Nat := 118140960795 + 2020503 * 2 ^ 59
def prefixEnd_2020503 : Nat := 4983230072969 + 3 ^ 40 * 2020503 * 2
def baseEnd_2020503 : Nat := 153702104126135334284501

theorem tailTrace_2020503 : CollatzResearch.WordTrace tailWord_2020503 prefixEnd_2020503 153702104126135334284501 := by
  unfold tailWord_2020503
  simp only [CollatzResearch.WordTrace]
  refine ⟨73693798599070180284730163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49129199066046786856486775 73693798599070180284730163)
  ·
    refine ⟨110540697898605270427095245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73693798599070180284730163 110540697898605270427095245)
    ·
      refine ⟨41452761711976976410160717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110540697898605270427095245 41452761711976976410160717)
      ·
        refine ⟨15544785641991366153810269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41452761711976976410160717 15544785641991366153810269)
        ·
          refine ⟨5829294615746762307678851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15544785641991366153810269 5829294615746762307678851)
          ·
            refine ⟨8743941923620143461518277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5829294615746762307678851 8743941923620143461518277)
            ·
              refine ⟨1639489110678776899034677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8743941923620143461518277 1639489110678776899034677)
              ·
                refine ⟨153702104126135334284501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1639489110678776899034677 153702104126135334284501)
                ·
                  rfl

theorem cell21_2020503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 4, 5].length) (baseStart_2020503 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2020503 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2020503 prefixEnd_2020503 := by exact prefixLift 2020503
  have htrace : WordTrace (prefixWord ++ tailWord_2020503) baseStart_2020503 baseEnd_2020503 := by
    simpa [prefixWord, tailWord_2020503, baseEnd_2020503] using wordTrace_append hprefix tailTrace_2020503
  have hstable : (prefixWord ++ tailWord_2020503).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2020503).length < 2 ^ (prefixWord ++ tailWord_2020503).sum := by decide
  have hdescent : baseEnd_2020503 < baseStart_2020503 := by decide
  rcases family_descends (prefixWord ++ tailWord_2020503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2020531 : List Nat := [1, 1, 1, 2, 3, 2, 4, 1, 6]
def baseStart_2020531 : Nat := 118140960795 + 2020531 * 2 ^ 59
def prefixEnd_2020531 : Nat := 4983230072969 + 3 ^ 40 * 2020531 * 2
def baseEnd_2020531 : Nat := 461112702359884176386779

theorem tailTrace_2020531 : CollatzResearch.WordTrace tailWord_2020531 prefixEnd_2020531 461112702359884176386779 := by
  unfold tailWord_2020531
  simp only [CollatzResearch.WordTrace]
  refine ⟨73694819842968741066749447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49129879895312494044499631 73694819842968741066749447)
  ·
    refine ⟨110542229764453111600124171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73694819842968741066749447 110542229764453111600124171)
    ·
      refine ⟨165813344646679667400186257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110542229764453111600124171 165813344646679667400186257)
      ·
        refine ⟨124360008485009750550139693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165813344646679667400186257 124360008485009750550139693)
        ·
          refine ⟨46635003181878656456302385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124360008485009750550139693 46635003181878656456302385)
          ·
            refine ⟨34976252386408992342226789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46635003181878656456302385 34976252386408992342226789)
            ·
              refine ⟨6558047322451686064167523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34976252386408992342226789 6558047322451686064167523)
              ·
                refine ⟨9837070983677529096251285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6558047322451686064167523 9837070983677529096251285)
                ·
                  refine ⟨461112702359884176386779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9837070983677529096251285 461112702359884176386779)
                  ·
                    rfl

theorem cell21_2020531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 4, 1, 6].length) (baseStart_2020531 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2020531 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2020531 prefixEnd_2020531 := by exact prefixLift 2020531
  have htrace : WordTrace (prefixWord ++ tailWord_2020531) baseStart_2020531 baseEnd_2020531 := by
    simpa [prefixWord, tailWord_2020531, baseEnd_2020531] using wordTrace_append hprefix tailTrace_2020531
  have hstable : (prefixWord ++ tailWord_2020531).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2020531).length < 2 ^ (prefixWord ++ tailWord_2020531).sum := by decide
  have hdescent : baseEnd_2020531 < baseStart_2020531 := by decide
  rcases family_descends (prefixWord ++ tailWord_2020531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2020562 : List Nat := [3, 2, 2, 2, 1, 1, 1, 9]
def baseStart_2020562 : Nat := 118140960795 + 2020562 * 2 ^ 59
def prefixEnd_2020562 : Nat := 4983230072969 + 3 ^ 40 * 2020562 * 2
def baseEnd_2020562 : Nat := 153706592327411670456683

theorem tailTrace_2020562 : CollatzResearch.WordTrace tailWord_2020562 prefixEnd_2020562 153706592327411670456683 := by
  unfold tailWord_2020562
  simp only [CollatzResearch.WordTrace]
  refine ⟨18423987626464108340281985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49130633670570955574085293 18423987626464108340281985)
  ·
    refine ⟨13817990719848081255211489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18423987626464108340281985 13817990719848081255211489)
    ·
      refine ⟨10363493039886060941408617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13817990719848081255211489 10363493039886060941408617)
      ·
        refine ⟨7772619779914545706056463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10363493039886060941408617 7772619779914545706056463)
        ·
          refine ⟨11658929669871818559084695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7772619779914545706056463 11658929669871818559084695)
          ·
            refine ⟨17488394504807727838627043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11658929669871818559084695 17488394504807727838627043)
            ·
              refine ⟨26232591757211591757940565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17488394504807727838627043 26232591757211591757940565)
              ·
                refine ⟨153706592327411670456683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 26232591757211591757940565 153706592327411670456683)
                ·
                  rfl

theorem cell21_2020562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 9].length) (baseStart_2020562 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2020562 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2020562 prefixEnd_2020562 := by exact prefixLift 2020562
  have htrace : WordTrace (prefixWord ++ tailWord_2020562) baseStart_2020562 baseEnd_2020562 := by
    simpa [prefixWord, tailWord_2020562, baseEnd_2020562] using wordTrace_append hprefix tailTrace_2020562
  have hstable : (prefixWord ++ tailWord_2020562).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2020562).length < 2 ^ (prefixWord ++ tailWord_2020562).sum := by decide
  have hdescent : baseEnd_2020562 < baseStart_2020562 := by decide
  rcases family_descends (prefixWord ++ tailWord_2020562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2020678 : List Nat := [6, 1, 1, 3, 1, 2, 1, 3, 3]
def baseStart_2020678 : Nat := 118140960795 + 2020678 * 2 ^ 59
def prefixEnd_2020678 : Nat := 4983230072969 + 3 ^ 40 * 2020678 * 2
def baseEnd_2020678 : Nat := 461146249762644587436479

theorem tailTrace_2020678 : CollatzResearch.WordTrace tailWord_2020678 prefixEnd_2020678 461146249762644587436479 := by
  unfold tailWord_2020678
  simp only [CollatzResearch.WordTrace]
  refine ⟨2303130667919880786635959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 49133454248957456781567125 2303130667919880786635959)
  ·
    refine ⟨3454696001879821179953939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2303130667919880786635959 3454696001879821179953939)
    ·
      refine ⟨5182044002819731769930909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3454696001879821179953939 5182044002819731769930909)
      ·
        refine ⟨1943266501057399413724091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5182044002819731769930909 1943266501057399413724091)
        ·
          refine ⟨2914899751586099120586137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1943266501057399413724091 2914899751586099120586137)
          ·
            refine ⟨2186174813689574340439603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2914899751586099120586137 2186174813689574340439603)
            ·
              refine ⟨3279262220534361510659405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2186174813689574340439603 3279262220534361510659405)
              ·
                refine ⟨1229723332700385566497277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3279262220534361510659405 1229723332700385566497277)
                ·
                  refine ⟨461146249762644587436479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1229723332700385566497277 461146249762644587436479)
                  ·
                    rfl

theorem cell21_2020678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 1, 3, 3].length) (baseStart_2020678 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2020678 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2020678 prefixEnd_2020678 := by exact prefixLift 2020678
  have htrace : WordTrace (prefixWord ++ tailWord_2020678) baseStart_2020678 baseEnd_2020678 := by
    simpa [prefixWord, tailWord_2020678, baseEnd_2020678] using wordTrace_append hprefix tailTrace_2020678
  have hstable : (prefixWord ++ tailWord_2020678).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2020678).length < 2 ^ (prefixWord ++ tailWord_2020678).sum := by decide
  have hdescent : baseEnd_2020678 < baseStart_2020678 := by decide
  rcases family_descends (prefixWord ++ tailWord_2020678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2020697 : List Nat := [1, 2, 1, 2, 2, 2, 11]
def baseStart_2020697 : Nat := 118140960795 + 2020697 * 2 ^ 59
def prefixEnd_2020697 : Nat := 4983230072969 + 3 ^ 40 * 2020697 * 2
def baseEnd_2020697 : Nat := 51238953980167197402197

theorem tailTrace_2020697 : CollatzResearch.WordTrace tailWord_2020697 prefixEnd_2020697 51238953980167197402197 := by
  unfold tailWord_2020697
  simp only [CollatzResearch.WordTrace]
  refine ⟨73700874360367351417292345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49133916240244900944861563 73700874360367351417292345)
  ·
    refine ⟨55275655770275513562969259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73700874360367351417292345 55275655770275513562969259)
    ·
      refine ⟨82913483655413270344453889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55275655770275513562969259 82913483655413270344453889)
      ·
        refine ⟨62185112741559952758340417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82913483655413270344453889 62185112741559952758340417)
        ·
          refine ⟨46638834556169964568755313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62185112741559952758340417 46638834556169964568755313)
          ·
            refine ⟨34979125917127473426566485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46638834556169964568755313 34979125917127473426566485)
            ·
              refine ⟨51238953980167197402197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 34979125917127473426566485 51238953980167197402197)
              ·
                rfl

theorem cell21_2020697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 11].length) (baseStart_2020697 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2020697 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2020697 prefixEnd_2020697 := by exact prefixLift 2020697
  have htrace : WordTrace (prefixWord ++ tailWord_2020697) baseStart_2020697 baseEnd_2020697 := by
    simpa [prefixWord, tailWord_2020697, baseEnd_2020697] using wordTrace_append hprefix tailTrace_2020697
  have hstable : (prefixWord ++ tailWord_2020697).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2020697).length < 2 ^ (prefixWord ++ tailWord_2020697).sum := by decide
  have hdescent : baseEnd_2020697 < baseStart_2020697 := by decide
  rcases family_descends (prefixWord ++ tailWord_2020697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2020717 : List Nat := [1, 5, 1, 1, 1, 3, 4, 1, 4]
def baseStart_2020717 : Nat := 118140960795 + 2020717 * 2 ^ 59
def prefixEnd_2020717 : Nat := 4983230072969 + 3 ^ 40 * 2020717 * 2
def baseEnd_2020717 : Nat := 461155150093989186286399

theorem tailTrace_2020717 : CollatzResearch.WordTrace tailWord_2020717 prefixEnd_2020717 461155150093989186286399 := by
  unfold tailWord_2020717
  simp only [CollatzResearch.WordTrace]
  refine ⟨73701603820294894833020405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49134402546863263222013603 73701603820294894833020405)
  ·
    refine ⟨6909525358152646390595663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 73701603820294894833020405 6909525358152646390595663)
    ·
      refine ⟨10364288037228969585893495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6909525358152646390595663 10364288037228969585893495)
      ·
        refine ⟨15546432055843454378840243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10364288037228969585893495 15546432055843454378840243)
        ·
          refine ⟨23319648083765181568260365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15546432055843454378840243 23319648083765181568260365)
          ·
            refine ⟨8744868031411943088097637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23319648083765181568260365 8744868031411943088097637)
            ·
              refine ⟨1639662755889739329018307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8744868031411943088097637 1639662755889739329018307)
              ·
                refine ⟨2459494133834608993527461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1639662755889739329018307 2459494133834608993527461)
                ·
                  refine ⟨461155150093989186286399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2459494133834608993527461 461155150093989186286399)
                  ·
                    rfl

theorem cell21_2020717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 4, 1, 4].length) (baseStart_2020717 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2020717 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2020717 prefixEnd_2020717 := by exact prefixLift 2020717
  have htrace : WordTrace (prefixWord ++ tailWord_2020717) baseStart_2020717 baseEnd_2020717 := by
    simpa [prefixWord, tailWord_2020717, baseEnd_2020717] using wordTrace_append hprefix tailTrace_2020717
  have hstable : (prefixWord ++ tailWord_2020717).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2020717).length < 2 ^ (prefixWord ++ tailWord_2020717).sum := by decide
  have hdescent : baseEnd_2020717 < baseStart_2020717 := by decide
  rcases family_descends (prefixWord ++ tailWord_2020717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2020754 : List Nat := [3, 2, 3, 3, 2, 1, 2, 2, 3]
def baseStart_2020754 : Nat := 118140960795 + 2020754 * 2 ^ 59
def prefixEnd_2020754 : Nat := 4983230072969 + 3 ^ 40 * 2020754 * 2
def baseEnd_2020754 : Nat := 461163593998085344169657

theorem tailTrace_2020754 : CollatzResearch.WordTrace tailWord_2020754 prefixEnd_2020754 461163593998085344169657 := by
  unfold tailWord_2020754
  simp only [CollatzResearch.WordTrace]
  refine ⟨18425738330290212538029329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49135302214107233434744877 18425738330290212538029329)
  ·
    refine ⟨13819303747717659403521997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18425738330290212538029329 13819303747717659403521997)
    ·
      refine ⟨5182238905394122276320749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13819303747717659403521997 5182238905394122276320749)
      ·
        refine ⟨1943339589522795853620281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5182238905394122276320749 1943339589522795853620281)
        ·
          refine ⟨1457504692142096890215211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1943339589522795853620281 1457504692142096890215211)
          ·
            refine ⟨2186257038213145335322817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1457504692142096890215211 2186257038213145335322817)
            ·
              refine ⟨1639692778659859001492113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2186257038213145335322817 1639692778659859001492113)
              ·
                refine ⟨1229769583994894251119085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1639692778659859001492113 1229769583994894251119085)
                ·
                  refine ⟨461163593998085344169657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1229769583994894251119085 461163593998085344169657)
                  ·
                    rfl

theorem cell21_2020754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 2, 2, 3].length) (baseStart_2020754 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2020754 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2020754 prefixEnd_2020754 := by exact prefixLift 2020754
  have htrace : WordTrace (prefixWord ++ tailWord_2020754) baseStart_2020754 baseEnd_2020754 := by
    simpa [prefixWord, tailWord_2020754, baseEnd_2020754] using wordTrace_append hprefix tailTrace_2020754
  have hstable : (prefixWord ++ tailWord_2020754).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2020754).length < 2 ^ (prefixWord ++ tailWord_2020754).sum := by decide
  have hdescent : baseEnd_2020754 < baseStart_2020754 := by decide
  rcases family_descends (prefixWord ++ tailWord_2020754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2020762 : List Nat := [3, 1, 1, 4, 1, 1, 3, 4, 3]
def baseStart_2020762 : Nat := 118140960795 + 2020762 * 2 ^ 59
def prefixEnd_2020762 : Nat := 4983230072969 + 3 ^ 40 * 2020762 * 2
def baseEnd_2020762 : Nat := 461165419707079108036307

theorem tailTrace_2020762 : CollatzResearch.WordTrace tailWord_2020762 prefixEnd_2020762 461165419707079108036307 := by
  unfold tailWord_2020762
  simp only [CollatzResearch.WordTrace]
  refine ⟨18425811276282966879602135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49135496736754578345605693 18425811276282966879602135)
  ·
    refine ⟨27638716914424450319403203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18425811276282966879602135 27638716914424450319403203)
    ·
      refine ⟨41458075371636675479104805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27638716914424450319403203 41458075371636675479104805)
      ·
        refine ⟨7773389132181876652332151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41458075371636675479104805 7773389132181876652332151)
        ·
          refine ⟨11660083698272814978498227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7773389132181876652332151 11660083698272814978498227)
          ·
            refine ⟨17490125547409222467747341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11660083698272814978498227 17490125547409222467747341)
            ·
              refine ⟨6558797080278458425405253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17490125547409222467747341 6558797080278458425405253)
              ·
                refine ⟨1229774452552210954763485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6558797080278458425405253 1229774452552210954763485)
                ·
                  refine ⟨461165419707079108036307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1229774452552210954763485 461165419707079108036307)
                  ·
                    rfl

theorem cell21_2020762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 3, 4, 3].length) (baseStart_2020762 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2020762 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2020762 prefixEnd_2020762 := by exact prefixLift 2020762
  have htrace : WordTrace (prefixWord ++ tailWord_2020762) baseStart_2020762 baseEnd_2020762 := by
    simpa [prefixWord, tailWord_2020762, baseEnd_2020762] using wordTrace_append hprefix tailTrace_2020762
  have hstable : (prefixWord ++ tailWord_2020762).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2020762).length < 2 ^ (prefixWord ++ tailWord_2020762).sum := by decide
  have hdescent : baseEnd_2020762 < baseStart_2020762 := by decide
  rcases family_descends (prefixWord ++ tailWord_2020762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2020773 : List Nat := [1, 3, 1, 2, 1, 1, 2, 10]
def baseStart_2020773 : Nat := 118140960795 + 2020773 * 2 ^ 59
def prefixEnd_2020773 : Nat := 4983230072969 + 3 ^ 40 * 2020773 * 2
def baseEnd_2020773 : Nat := 153722643352315177784317

theorem tailTrace_2020773 : CollatzResearch.WordTrace tailWord_2020773 prefixEnd_2020773 153722643352315177784317 := by
  unfold tailWord_2020773
  simp only [CollatzResearch.WordTrace]
  refine ⟨73703646308092016397058973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49135764205394677598039315 73703646308092016397058973)
  ·
    refine ⟨27638867365534506148897115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73703646308092016397058973 27638867365534506148897115)
    ·
      refine ⟨41458301048301759223345673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27638867365534506148897115 41458301048301759223345673)
      ·
        refine ⟨31093725786226319417509255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41458301048301759223345673 31093725786226319417509255)
        ·
          refine ⟨46640588679339479126263883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31093725786226319417509255 46640588679339479126263883)
          ·
            refine ⟨69960883019009218689395825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46640588679339479126263883 69960883019009218689395825)
            ·
              refine ⟨52470662264256914017046869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69960883019009218689395825 52470662264256914017046869)
              ·
                refine ⟨153722643352315177784317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 52470662264256914017046869 153722643352315177784317)
                ·
                  rfl

theorem cell21_2020773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 10].length) (baseStart_2020773 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2020773 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2020773 prefixEnd_2020773 := by exact prefixLift 2020773
  have htrace : WordTrace (prefixWord ++ tailWord_2020773) baseStart_2020773 baseEnd_2020773 := by
    simpa [prefixWord, tailWord_2020773, baseEnd_2020773] using wordTrace_append hprefix tailTrace_2020773
  have hstable : (prefixWord ++ tailWord_2020773).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2020773).length < 2 ^ (prefixWord ++ tailWord_2020773).sum := by decide
  have hdescent : baseEnd_2020773 < baseStart_2020773 := by decide
  rcases family_descends (prefixWord ++ tailWord_2020773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2020821 : List Nat := [1, 3, 2, 3, 1, 1, 4, 1, 5]
def baseStart_2020821 : Nat := 118140960795 + 2020821 * 2 ^ 59
def prefixEnd_2020821 : Nat := 4983230072969 + 3 ^ 40 * 2020821 * 2
def baseEnd_2020821 : Nat := 461178884310908116552853

theorem tailTrace_2020821 : CollatzResearch.WordTrace tailWord_2020821 prefixEnd_2020821 461178884310908116552853 := by
  unfold tailWord_2020821
  simp only [CollatzResearch.WordTrace]
  refine ⟨73705397011918120594806317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49136931341278747063204211 73705397011918120594806317)
  ·
    refine ⟨27639523879469295223052369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73705397011918120594806317 27639523879469295223052369)
    ·
      refine ⟨20729642909601971417289277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27639523879469295223052369 20729642909601971417289277)
      ·
        refine ⟨7773616091100739281483479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20729642909601971417289277 7773616091100739281483479)
        ·
          refine ⟨11660424136651108922225219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7773616091100739281483479 11660424136651108922225219)
          ·
            refine ⟨17490636204976663383337829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11660424136651108922225219 17490636204976663383337829)
            ·
              refine ⟨3279494288433124384375843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17490636204976663383337829 3279494288433124384375843)
              ·
                refine ⟨4919241432649686576563765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3279494288433124384375843 4919241432649686576563765)
                ·
                  refine ⟨461178884310908116552853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4919241432649686576563765 461178884310908116552853)
                  ·
                    rfl

theorem cell21_2020821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 4, 1, 5].length) (baseStart_2020821 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2020821 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2020821 prefixEnd_2020821 := by exact prefixLift 2020821
  have htrace : WordTrace (prefixWord ++ tailWord_2020821) baseStart_2020821 baseEnd_2020821 := by
    simpa [prefixWord, tailWord_2020821, baseEnd_2020821] using wordTrace_append hprefix tailTrace_2020821
  have hstable : (prefixWord ++ tailWord_2020821).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2020821).length < 2 ^ (prefixWord ++ tailWord_2020821).sum := by decide
  have hdescent : baseEnd_2020821 < baseStart_2020821 := by decide
  rcases family_descends (prefixWord ++ tailWord_2020821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2020925 : List Nat := [1, 4, 1, 3, 12]
def baseStart_2020925 : Nat := 118140960795 + 2020925 * 2 ^ 59
def prefixEnd_2020925 : Nat := 4983230072969 + 3 ^ 40 * 2020925 * 2
def baseEnd_2020925 : Nat := 5693859487997864775547

theorem tailTrace_2020925 : CollatzResearch.WordTrace tailWord_2020925 prefixEnd_2020925 5693859487997864775547 := by
  unfold tailWord_2020925
  simp only [CollatzResearch.WordTrace]
  refine ⟨73709190203541346356592229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49139460135694230904394819 73709190203541346356592229)
  ·
    refine ⟨13820473163164002441861043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73709190203541346356592229 13820473163164002441861043)
    ·
      refine ⟨20730709744746003662791565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13820473163164002441861043 20730709744746003662791565)
      ·
        refine ⟨7774016154279751373546837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20730709744746003662791565 7774016154279751373546837)
        ·
          refine ⟨5693859487997864775547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 7774016154279751373546837 5693859487997864775547)
          ·
            rfl

theorem cell21_2020925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 12].length) (baseStart_2020925 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2020925 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2020925 prefixEnd_2020925 := by exact prefixLift 2020925
  have htrace : WordTrace (prefixWord ++ tailWord_2020925) baseStart_2020925 baseEnd_2020925 := by
    simpa [prefixWord, tailWord_2020925, baseEnd_2020925] using wordTrace_append hprefix tailTrace_2020925
  have hstable : (prefixWord ++ tailWord_2020925).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2020925).length < 2 ^ (prefixWord ++ tailWord_2020925).sum := by decide
  have hdescent : baseEnd_2020925 < baseStart_2020925 := by decide
  rcases family_descends (prefixWord ++ tailWord_2020925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2021004 : List Nat := [2, 2, 1, 2, 1, 1, 7, 1, 4]
def baseStart_2021004 : Nat := 118140960795 + 2021004 * 2 ^ 59
def prefixEnd_2021004 : Nat := 4983230072969 + 3 ^ 40 * 2021004 * 2
def baseEnd_2021004 : Nat := 461220647404140465002479

theorem tailTrace_2021004 : CollatzResearch.WordTrace tailWord_2021004 prefixEnd_2021004 461220647404140465002479 := by
  unfold tailWord_2021004
  simp only [CollatzResearch.WordTrace]
  refine ⟨36856035785127571424359033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49141381046836761899145377 36856035785127571424359033)
  ·
    refine ⟨27642026838845678568269275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36856035785127571424359033 27642026838845678568269275)
    ·
      refine ⟨41463040258268517852403913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27642026838845678568269275 41463040258268517852403913)
      ·
        refine ⟨31097280193701388389302935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41463040258268517852403913 31097280193701388389302935)
        ·
          refine ⟨46645920290552082583954403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31097280193701388389302935 46645920290552082583954403)
          ·
            refine ⟨69968880435828123875931605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46645920290552082583954403 69968880435828123875931605)
            ·
              refine ⟨1639895635214721653342147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 69968880435828123875931605 1639895635214721653342147)
              ·
                refine ⟨2459843452822082480013221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1639895635214721653342147 2459843452822082480013221)
                ·
                  refine ⟨461220647404140465002479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2459843452822082480013221 461220647404140465002479)
                  ·
                    rfl

theorem cell21_2021004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 7, 1, 4].length) (baseStart_2021004 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2021004 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2021004 prefixEnd_2021004 := by exact prefixLift 2021004
  have htrace : WordTrace (prefixWord ++ tailWord_2021004) baseStart_2021004 baseEnd_2021004 := by
    simpa [prefixWord, tailWord_2021004, baseEnd_2021004] using wordTrace_append hprefix tailTrace_2021004
  have hstable : (prefixWord ++ tailWord_2021004).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2021004).length < 2 ^ (prefixWord ++ tailWord_2021004).sum := by decide
  have hdescent : baseEnd_2021004 < baseStart_2021004 := by decide
  rcases family_descends (prefixWord ++ tailWord_2021004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2021049 : List Nat := [1, 2, 1, 4, 1, 1, 2, 6, 3]
def baseStart_2021049 : Nat := 118140960795 + 2021049 * 2 ^ 59
def prefixEnd_2021049 : Nat := 4983230072969 + 3 ^ 40 * 2021049 * 2
def baseEnd_2021049 : Nat := 461230917017230386752387

theorem tailTrace_2021049 : CollatzResearch.WordTrace tailWord_2021049 prefixEnd_2021049 461230917017230386752387 := by
  unfold tailWord_2021049
  simp only [CollatzResearch.WordTrace]
  refine ⟨73713712855092115534106201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49142475236728077022737467 73713712855092115534106201)
  ·
    refine ⟨55285284641319086650579651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73713712855092115534106201 55285284641319086650579651)
    ·
      refine ⟨82927926961978629975869477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55285284641319086650579651 82927926961978629975869477)
      ·
        refine ⟨15548986305370993120475527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82927926961978629975869477 15548986305370993120475527)
        ·
          refine ⟨23323479458056489680713291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15548986305370993120475527 23323479458056489680713291)
          ·
            refine ⟨34985219187084734521069937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23323479458056489680713291 34985219187084734521069937)
            ·
              refine ⟨26238914390313550890802453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34985219187084734521069937 26238914390313550890802453)
              ·
                refine ⟨1229949112045947698006365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 26238914390313550890802453 1229949112045947698006365)
                ·
                  refine ⟨461230917017230386752387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1229949112045947698006365 461230917017230386752387)
                  ·
                    rfl

theorem cell21_2021049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 6, 3].length) (baseStart_2021049 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2021049 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2021049 prefixEnd_2021049 := by exact prefixLift 2021049
  have htrace : WordTrace (prefixWord ++ tailWord_2021049) baseStart_2021049 baseEnd_2021049 := by
    simpa [prefixWord, tailWord_2021049, baseEnd_2021049] using wordTrace_append hprefix tailTrace_2021049
  have hstable : (prefixWord ++ tailWord_2021049).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2021049).length < 2 ^ (prefixWord ++ tailWord_2021049).sum := by decide
  have hdescent : baseEnd_2021049 < baseStart_2021049 := by decide
  rcases family_descends (prefixWord ++ tailWord_2021049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2021063 : List Nat := [1, 1, 4, 1, 1, 1, 5, 3, 4]
def baseStart_2021063 : Nat := 118140960795 + 2021063 * 2 ^ 59
def prefixEnd_2021063 : Nat := 4983230072969 + 3 ^ 40 * 2021063 * 2
def baseEnd_2021063 : Nat := 461234112007969473519025

theorem tailTrace_2021063 : CollatzResearch.WordTrace tailWord_2021063 prefixEnd_2021063 461234112007969473519025 := by
  unfold tailWord_2021063
  simp only [CollatzResearch.WordTrace]
  refine ⟨73714223477041395925115843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49142815651360930616743895 73714223477041395925115843)
  ·
    refine ⟨110571335215562093887673765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73714223477041395925115843 110571335215562093887673765)
    ·
      refine ⟨20732125352917892603938831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 110571335215562093887673765 20732125352917892603938831)
      ·
        refine ⟨31098188029376838905908247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20732125352917892603938831 31098188029376838905908247)
        ·
          refine ⟨46647282044065258358862371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31098188029376838905908247 46647282044065258358862371)
          ·
            refine ⟨69970923066097887538293557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46647282044065258358862371 69970923066097887538293557)
            ·
              refine ⟨6559774037446676956715021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 69970923066097887538293557 6559774037446676956715021)
              ·
                refine ⟨2459915264042503858768133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6559774037446676956715021 2459915264042503858768133)
                ·
                  refine ⟨461234112007969473519025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2459915264042503858768133 461234112007969473519025)
                  ·
                    rfl

theorem cell21_2021063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 5, 3, 4].length) (baseStart_2021063 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2021063 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2021063 prefixEnd_2021063 := by exact prefixLift 2021063
  have htrace : WordTrace (prefixWord ++ tailWord_2021063) baseStart_2021063 baseEnd_2021063 := by
    simpa [prefixWord, tailWord_2021063, baseEnd_2021063] using wordTrace_append hprefix tailTrace_2021063
  have hstable : (prefixWord ++ tailWord_2021063).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2021063).length < 2 ^ (prefixWord ++ tailWord_2021063).sum := by decide
  have hdescent : baseEnd_2021063 < baseStart_2021063 := by decide
  rcases family_descends (prefixWord ++ tailWord_2021063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2021153 : List Nat := [1, 2, 3, 2, 1, 4, 8]
def baseStart_2021153 : Nat := 118140960795 + 2021153 * 2 ^ 59
def prefixEnd_2021153 : Nat := 4983230072969 + 3 ^ 40 * 2021153 * 2
def baseEnd_2021153 : Nat := 51250516803794368557649

theorem tailTrace_2021153 : CollatzResearch.WordTrace tailWord_2021153 prefixEnd_2021153 51250516803794368557649 := by
  unfold tailWord_2021153
  simp only [CollatzResearch.WordTrace]
  refine ⟨73717506046715341295892113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49145004031143560863928075 73717506046715341295892113)
  ·
    refine ⟨55288129535036505971919085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73717506046715341295892113 55288129535036505971919085)
    ·
      refine ⟨20733048575638689739469657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55288129535036505971919085 20733048575638689739469657)
      ·
        refine ⟨15549786431729017304602243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20733048575638689739469657 15549786431729017304602243)
        ·
          refine ⟨23324679647593525956903365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15549786431729017304602243 23324679647593525956903365)
          ·
            refine ⟨4373377433923786116919381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23324679647593525956903365 4373377433923786116919381)
            ·
              refine ⟨51250516803794368557649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4373377433923786116919381 51250516803794368557649)
              ·
                rfl

theorem cell21_2021153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 8].length) (baseStart_2021153 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2021153 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2021153 prefixEnd_2021153 := by exact prefixLift 2021153
  have htrace : WordTrace (prefixWord ++ tailWord_2021153) baseStart_2021153 baseEnd_2021153 := by
    simpa [prefixWord, tailWord_2021153, baseEnd_2021153] using wordTrace_append hprefix tailTrace_2021153
  have hstable : (prefixWord ++ tailWord_2021153).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2021153).length < 2 ^ (prefixWord ++ tailWord_2021153).sum := by decide
  have hdescent : baseEnd_2021153 < baseStart_2021153 := by decide
  rcases family_descends (prefixWord ++ tailWord_2021153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2021156 : List Nat := [2, 3, 1, 3, 2, 1, 3, 2, 4]
def baseStart_2021156 : Nat := 118140960795 + 2021156 * 2 ^ 59
def prefixEnd_2021156 : Nat := 4983230072969 + 3 ^ 40 * 2021156 * 2
def baseEnd_2021156 : Nat := 461255335875021978468835

theorem tailTrace_2021156 : CollatzResearch.WordTrace tailWord_2021156 prefixEnd_2021156 461255335875021978468835 := by
  unfold tailWord_2021156
  simp only [CollatzResearch.WordTrace]
  refine ⟨36858807732852236404125661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49145076977136315205500881 36858807732852236404125661)
  ·
    refine ⟨13822052899819588651547123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36858807732852236404125661 13822052899819588651547123)
    ·
      refine ⟨20733079349729382977320685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13822052899819588651547123 20733079349729382977320685)
      ·
        refine ⟨7774904756148518616495257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20733079349729382977320685 7774904756148518616495257)
        ·
          refine ⟨5831178567111388962371443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7774904756148518616495257 5831178567111388962371443)
          ·
            refine ⟨8746767850667083443557165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5831178567111388962371443 8746767850667083443557165)
            ·
              refine ⟨3280037944000156291333937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8746767850667083443557165 3280037944000156291333937)
              ·
                refine ⟨2460028458000117218500453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3280037944000156291333937 2460028458000117218500453)
                ·
                  refine ⟨461255335875021978468835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2460028458000117218500453 461255335875021978468835)
                  ·
                    rfl

theorem cell21_2021156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 3, 2, 4].length) (baseStart_2021156 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2021156 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2021156 prefixEnd_2021156 := by exact prefixLift 2021156
  have htrace : WordTrace (prefixWord ++ tailWord_2021156) baseStart_2021156 baseEnd_2021156 := by
    simpa [prefixWord, tailWord_2021156, baseEnd_2021156] using wordTrace_append hprefix tailTrace_2021156
  have hstable : (prefixWord ++ tailWord_2021156).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2021156).length < 2 ^ (prefixWord ++ tailWord_2021156).sum := by decide
  have hdescent : baseEnd_2021156 < baseStart_2021156 := by decide
  rcases family_descends (prefixWord ++ tailWord_2021156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2021167 : List Nat := [1, 1, 2, 1, 2, 1, 2, 2, 9]
def baseStart_2021167 : Nat := 118140960795 + 2021167 * 2 ^ 59
def prefixEnd_2021167 : Nat := 4983230072969 + 3 ^ 40 * 2021167 * 2
def baseEnd_2021167 : Nat := 461257846224888403785479

theorem tailTrace_2021167 : CollatzResearch.WordTrace tailWord_2021167 prefixEnd_2021167 461257846224888403785479 := by
  unfold tailWord_2021167
  simp only [CollatzResearch.WordTrace]
  refine ⟨73718016668664621686901755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49145344445776414457934503 73718016668664621686901755)
  ·
    refine ⟨110577025002996932530352633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73718016668664621686901755 110577025002996932530352633)
    ·
      refine ⟨82932768752247699397764475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110577025002996932530352633 82932768752247699397764475)
      ·
        refine ⟨124399153128371549096646713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82932768752247699397764475 124399153128371549096646713)
        ·
          refine ⟨93299364846278661822485035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124399153128371549096646713 93299364846278661822485035)
          ·
            refine ⟨139949047269417992733727553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93299364846278661822485035 139949047269417992733727553)
            ·
              refine ⟨104961785452063494550295665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139949047269417992733727553 104961785452063494550295665)
              ·
                refine ⟨78721339089047620912721749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104961785452063494550295665 78721339089047620912721749)
                ·
                  refine ⟨461257846224888403785479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 78721339089047620912721749 461257846224888403785479)
                  ·
                    rfl

theorem cell21_2021167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 2, 9].length) (baseStart_2021167 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2021167 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2021167 prefixEnd_2021167 := by exact prefixLift 2021167
  have htrace : WordTrace (prefixWord ++ tailWord_2021167) baseStart_2021167 baseEnd_2021167 := by
    simpa [prefixWord, tailWord_2021167, baseEnd_2021167] using wordTrace_append hprefix tailTrace_2021167
  have hstable : (prefixWord ++ tailWord_2021167).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2021167).length < 2 ^ (prefixWord ++ tailWord_2021167).sum := by decide
  have hdescent : baseEnd_2021167 < baseStart_2021167 := by decide
  rcases family_descends (prefixWord ++ tailWord_2021167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2021173 : List Nat := [1, 3, 3, 1, 4, 1, 3, 1, 4]
def baseStart_2021173 : Nat := 118140960795 + 2021173 * 2 ^ 59
def prefixEnd_2021173 : Nat := 4983230072969 + 3 ^ 40 * 2021173 * 2
def baseEnd_2021173 : Nat := 461259215506633726685467

theorem tailTrace_2021173 : CollatzResearch.WordTrace tailWord_2021173 prefixEnd_2021173 461259215506633726685467 := by
  unfold tailWord_2021173
  simp only [CollatzResearch.WordTrace]
  refine ⟨73718235506642884711620173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49145490337761923141080115 73718235506642884711620173)
  ·
    refine ⟨27644338314991081766857565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73718235506642884711620173 27644338314991081766857565)
    ·
      refine ⟨10366626868121655662571587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27644338314991081766857565 10366626868121655662571587)
      ·
        refine ⟨15549940302182483493857381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10366626868121655662571587 15549940302182483493857381)
        ·
          refine ⟨2915613806659215655098259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15549940302182483493857381 2915613806659215655098259)
          ·
            refine ⟨4373420709988823482647389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2915613806659215655098259 4373420709988823482647389)
            ·
              refine ⟨1640032766245808805992771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4373420709988823482647389 1640032766245808805992771)
              ·
                refine ⟨2460049149368713208989157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1640032766245808805992771 2460049149368713208989157)
                ·
                  refine ⟨461259215506633726685467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2460049149368713208989157 461259215506633726685467)
                  ·
                    rfl

theorem cell21_2021173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 3, 1, 4].length) (baseStart_2021173 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2021173 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2021173 prefixEnd_2021173 := by exact prefixLift 2021173
  have htrace : WordTrace (prefixWord ++ tailWord_2021173) baseStart_2021173 baseEnd_2021173 := by
    simpa [prefixWord, tailWord_2021173, baseEnd_2021173] using wordTrace_append hprefix tailTrace_2021173
  have hstable : (prefixWord ++ tailWord_2021173).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2021173).length < 2 ^ (prefixWord ++ tailWord_2021173).sum := by decide
  have hdescent : baseEnd_2021173 < baseStart_2021173 := by decide
  rcases family_descends (prefixWord ++ tailWord_2021173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2021218 : List Nat := [3, 3, 2, 1, 2, 3, 1, 1, 5]
def baseStart_2021218 : Nat := 118140960795 + 2021218 * 2 ^ 59
def prefixEnd_2021218 : Nat := 4983230072969 + 3 ^ 40 * 2021218 * 2
def baseEnd_2021218 : Nat := 461269485119723648435375

theorem tailTrace_2021218 : CollatzResearch.WordTrace tailWord_2021218 prefixEnd_2021218 461269485119723648435375 := by
  unfold tailWord_2021218
  simp only [CollatzResearch.WordTrace]
  refine ⟨18429969197869964349252077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49146584527653238264672205 18429969197869964349252077)
  ·
    refine ⟨6911238449201236630969529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18429969197869964349252077 6911238449201236630969529)
    ·
      refine ⟨5183428836900927473227147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6911238449201236630969529 5183428836900927473227147)
      ·
        refine ⟨7775143255351391209840721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5183428836900927473227147 7775143255351391209840721)
        ·
          refine ⟨5831357441513543407380541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7775143255351391209840721 5831357441513543407380541)
          ·
            refine ⟨2186759040567578777767703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5831357441513543407380541 2186759040567578777767703)
            ·
              refine ⟨3280138560851368166651555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2186759040567578777767703 3280138560851368166651555)
              ·
                refine ⟨4920207841277052249977333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3280138560851368166651555 4920207841277052249977333)
                ·
                  refine ⟨461269485119723648435375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4920207841277052249977333 461269485119723648435375)
                  ·
                    rfl

theorem cell21_2021218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 1, 1, 5].length) (baseStart_2021218 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2021218 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2021218 prefixEnd_2021218 := by exact prefixLift 2021218
  have htrace : WordTrace (prefixWord ++ tailWord_2021218) baseStart_2021218 baseEnd_2021218 := by
    simpa [prefixWord, tailWord_2021218, baseEnd_2021218] using wordTrace_append hprefix tailTrace_2021218
  have hstable : (prefixWord ++ tailWord_2021218).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2021218).length < 2 ^ (prefixWord ++ tailWord_2021218).sum := by decide
  have hdescent : baseEnd_2021218 < baseStart_2021218 := by decide
  rcases family_descends (prefixWord ++ tailWord_2021218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2021229 : List Nat := [1, 5, 1, 1, 1, 1, 3, 8]
def baseStart_2021229 : Nat := 118140960795 + 2021229 * 2 ^ 59
def prefixEnd_2021229 : Nat := 4983230072969 + 3 ^ 40 * 2021229 * 2
def baseEnd_2021229 : Nat := 153757331823196691250673

theorem tailTrace_2021229 : CollatzResearch.WordTrace tailWord_2021229 prefixEnd_2021229 153757331823196691250673 := by
  unfold tailWord_2021229
  simp only [CollatzResearch.WordTrace]
  refine ⟨73720277994440006275658741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49146851996293337517105827 73720277994440006275658741)
  ·
    refine ⟨6911276061978750588343007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 73720277994440006275658741 6911276061978750588343007)
    ·
      refine ⟨10366914092968125882514511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6911276061978750588343007 10366914092968125882514511)
      ·
        refine ⟨15550371139452188823771767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10366914092968125882514511 15550371139452188823771767)
        ·
          refine ⟨23325556709178283235657651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15550371139452188823771767 23325556709178283235657651)
          ·
            refine ⟨34988335063767424853486477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23325556709178283235657651 34988335063767424853486477)
            ·
              refine ⟨13120625648912784320057429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34988335063767424853486477 13120625648912784320057429)
              ·
                refine ⟨153757331823196691250673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13120625648912784320057429 153757331823196691250673)
                ·
                  rfl

theorem cell21_2021229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 8].length) (baseStart_2021229 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2021229 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2021229 prefixEnd_2021229 := by exact prefixLift 2021229
  have htrace : WordTrace (prefixWord ++ tailWord_2021229) baseStart_2021229 baseEnd_2021229 := by
    simpa [prefixWord, tailWord_2021229, baseEnd_2021229] using wordTrace_append hprefix tailTrace_2021229
  have hstable : (prefixWord ++ tailWord_2021229).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2021229).length < 2 ^ (prefixWord ++ tailWord_2021229).sum := by decide
  have hdescent : baseEnd_2021229 < baseStart_2021229 := by decide
  rcases family_descends (prefixWord ++ tailWord_2021229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2021243 : List Nat := [1, 1, 1, 1, 1, 5, 1, 3, 7]
def baseStart_2021243 : Nat := 118140960795 + 2021243 * 2 ^ 59
def prefixEnd_2021243 : Nat := 4983230072969 + 3 ^ 40 * 2021243 * 2
def baseEnd_2021243 : Nat := 461275190460329160518657

theorem tailTrace_2021243 : CollatzResearch.WordTrace tailWord_2021243 prefixEnd_2021243 461275190460329160518657 := by
  unfold tailWord_2021243
  simp only [CollatzResearch.WordTrace]
  refine ⟨73720788616389286666668383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49147192410926191111112255 73720788616389286666668383)
  ·
    refine ⟨110581182924583930000002575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73720788616389286666668383 110581182924583930000002575)
    ·
      refine ⟨165871774386875895000003863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110581182924583930000002575 165871774386875895000003863)
      ·
        refine ⟨248807661580313842500005795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165871774386875895000003863 248807661580313842500005795)
        ·
          refine ⟨373211492370470763750008693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248807661580313842500005795 373211492370470763750008693)
          ·
            refine ⟨34988577409731634101563315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 373211492370470763750008693 34988577409731634101563315)
            ·
              refine ⟨52482866114597451152344973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34988577409731634101563315 52482866114597451152344973)
              ·
                refine ⟨19681074792974044182129365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52482866114597451152344973 19681074792974044182129365)
                ·
                  refine ⟨461275190460329160518657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19681074792974044182129365 461275190460329160518657)
                  ·
                    rfl

theorem cell21_2021243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 3, 7].length) (baseStart_2021243 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2021243 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2021243 prefixEnd_2021243 := by exact prefixLift 2021243
  have htrace : WordTrace (prefixWord ++ tailWord_2021243) baseStart_2021243 baseEnd_2021243 := by
    simpa [prefixWord, tailWord_2021243, baseEnd_2021243] using wordTrace_append hprefix tailTrace_2021243
  have hstable : (prefixWord ++ tailWord_2021243).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2021243).length < 2 ^ (prefixWord ++ tailWord_2021243).sum := by decide
  have hdescent : baseEnd_2021243 < baseStart_2021243 := by decide
  rcases family_descends (prefixWord ++ tailWord_2021243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2021319 : List Nat := [1, 1, 4, 1, 1, 2, 1, 1, 9]
def baseStart_2021319 : Nat := 118140960795 + 2021319 * 2 ^ 59
def prefixEnd_2021319 : Nat := 4983230072969 + 3 ^ 40 * 2021319 * 2
def baseEnd_2021319 : Nat := 461292534695769917251835

theorem tailTrace_2021319 : CollatzResearch.WordTrace tailWord_2021319 prefixEnd_2021319 461292534695769917251835 := by
  unfold tailWord_2021319
  simp only [CollatzResearch.WordTrace]
  refine ⟨73723560564113951646435011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49149040376075967764290007 73723560564113951646435011)
  ·
    refine ⟨110585340846170927469652517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73723560564113951646435011 110585340846170927469652517)
    ·
      refine ⟨20734751408657048900559847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 110585340846170927469652517 20734751408657048900559847)
      ·
        refine ⟨31102127112985573350839771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20734751408657048900559847 31102127112985573350839771)
        ·
          refine ⟨46653190669478360026259657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31102127112985573350839771 46653190669478360026259657)
          ·
            refine ⟨34989893002108770019694743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46653190669478360026259657 34989893002108770019694743)
            ·
              refine ⟨52484839503163155029542115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34989893002108770019694743 52484839503163155029542115)
              ·
                refine ⟨78727259254744732544313173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52484839503163155029542115 78727259254744732544313173)
                ·
                  refine ⟨461292534695769917251835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 78727259254744732544313173 461292534695769917251835)
                  ·
                    rfl

theorem cell21_2021319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 1, 9].length) (baseStart_2021319 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2021319 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2021319 prefixEnd_2021319 := by exact prefixLift 2021319
  have htrace : WordTrace (prefixWord ++ tailWord_2021319) baseStart_2021319 baseEnd_2021319 := by
    simpa [prefixWord, tailWord_2021319, baseEnd_2021319] using wordTrace_append hprefix tailTrace_2021319
  have hstable : (prefixWord ++ tailWord_2021319).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2021319).length < 2 ^ (prefixWord ++ tailWord_2021319).sum := by decide
  have hdescent : baseEnd_2021319 < baseStart_2021319 := by decide
  rcases family_descends (prefixWord ++ tailWord_2021319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2021336 : List Nat := [2, 1, 2, 2, 2, 2, 4, 1, 5]
def baseStart_2021336 : Nat := 118140960795 + 2021336 * 2 ^ 59
def prefixEnd_2021336 : Nat := 4983230072969 + 3 ^ 40 * 2021336 * 2
def baseEnd_2021336 : Nat := 461296414327381665468467

theorem tailTrace_2021336 : CollatzResearch.WordTrace tailWord_2021336 prefixEnd_2021336 461296414327381665468467 := by
  unfold tailWord_2021336
  simp only [CollatzResearch.WordTrace]
  refine ⟨36862090302526181774901931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49149453736701575699869241 36862090302526181774901931)
  ·
    refine ⟨55293135453789272662352897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36862090302526181774901931 55293135453789272662352897)
    ·
      refine ⟨41469851590341954496764673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55293135453789272662352897 41469851590341954496764673)
      ·
        refine ⟨31102388692756465872573505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41469851590341954496764673 31102388692756465872573505)
        ·
          refine ⟨23326791519567349404430129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31102388692756465872573505 23326791519567349404430129)
          ·
            refine ⟨17495093639675512053322597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23326791519567349404430129 17495093639675512053322597)
            ·
              refine ⟨3280330057439158509997987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17495093639675512053322597 3280330057439158509997987)
              ·
                refine ⟨4920495086158737764996981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3280330057439158509997987 4920495086158737764996981)
                ·
                  refine ⟨461296414327381665468467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4920495086158737764996981 461296414327381665468467)
                  ·
                    rfl

theorem cell21_2021336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 4, 1, 5].length) (baseStart_2021336 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2021336 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2021336 prefixEnd_2021336 := by exact prefixLift 2021336
  have htrace : WordTrace (prefixWord ++ tailWord_2021336) baseStart_2021336 baseEnd_2021336 := by
    simpa [prefixWord, tailWord_2021336, baseEnd_2021336] using wordTrace_append hprefix tailTrace_2021336
  have hstable : (prefixWord ++ tailWord_2021336).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2021336).length < 2 ^ (prefixWord ++ tailWord_2021336).sum := by decide
  have hdescent : baseEnd_2021336 < baseStart_2021336 := by decide
  rcases family_descends (prefixWord ++ tailWord_2021336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2021381 : List Nat := [1, 3, 1, 1, 2, 6, 7]
def baseStart_2021381 : Nat := 118140960795 + 2021381 * 2 ^ 59
def prefixEnd_2021381 : Nat := 4983230072969 + 3 ^ 40 * 2021381 * 2
def baseEnd_2021381 : Nat := 51256298215607954135375

theorem tailTrace_2021381 : CollatzResearch.WordTrace tailWord_2021381 prefixEnd_2021381 51256298215607954135375 := by
  unfold tailWord_2021381
  simp only [CollatzResearch.WordTrace]
  refine ⟨73725821889889336235191997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49150547926592890823461331 73725821889889336235191997)
  ·
    refine ⟨27647183208708501088196999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73725821889889336235191997 27647183208708501088196999)
    ·
      refine ⟨41470774813062751632295499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27647183208708501088196999 41470774813062751632295499)
      ·
        refine ⟨62206162219594127448443249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41470774813062751632295499 62206162219594127448443249)
        ·
          refine ⟨46654621664695595586332437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62206162219594127448443249 46654621664695595586332437)
          ·
            refine ⟨2186935390532606043109333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 46654621664695595586332437 2186935390532606043109333)
            ·
              refine ⟨51256298215607954135375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2186935390532606043109333 51256298215607954135375)
              ·
                rfl

theorem cell21_2021381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 7].length) (baseStart_2021381 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2021381 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2021381 prefixEnd_2021381 := by exact prefixLift 2021381
  have htrace : WordTrace (prefixWord ++ tailWord_2021381) baseStart_2021381 baseEnd_2021381 := by
    simpa [prefixWord, tailWord_2021381, baseEnd_2021381] using wordTrace_append hprefix tailTrace_2021381
  have hstable : (prefixWord ++ tailWord_2021381).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2021381).length < 2 ^ (prefixWord ++ tailWord_2021381).sum := by decide
  have hdescent : baseEnd_2021381 < baseStart_2021381 := by decide
  rcases family_descends (prefixWord ++ tailWord_2021381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2021440 : List Nat := [2, 1, 1, 2, 2, 13]
def baseStart_2021440 : Nat := 118140960795 + 2021440 * 2 ^ 59
def prefixEnd_2021440 : Nat := 4983230072969 + 3 ^ 40 * 2021440 * 2
def baseEnd_2021440 : Nat := 17085931427566688730923

theorem tailTrace_2021440 : CollatzResearch.WordTrace tailWord_2021440 prefixEnd_2021440 17085931427566688730923 := by
  unfold tailWord_2021440
  simp only [CollatzResearch.WordTrace]
  refine ⟨36863986898337794655794887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49151982531117059541059849 36863986898337794655794887)
  ·
    refine ⟨55295980347506691983692331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36863986898337794655794887 55295980347506691983692331)
    ·
      refine ⟨82943970521260037975538497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55295980347506691983692331 82943970521260037975538497)
      ·
        refine ⟨62207977890945028481653873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82943970521260037975538497 62207977890945028481653873)
        ·
          refine ⟨46655983418208771361240405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62207977890945028481653873 46655983418208771361240405)
          ·
            refine ⟨17085931427566688730923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 46655983418208771361240405 17085931427566688730923)
            ·
              rfl

theorem cell21_2021440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 13].length) (baseStart_2021440 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2021440 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2021440 prefixEnd_2021440 := by exact prefixLift 2021440
  have htrace : WordTrace (prefixWord ++ tailWord_2021440) baseStart_2021440 baseEnd_2021440 := by
    simpa [prefixWord, tailWord_2021440, baseEnd_2021440] using wordTrace_append hprefix tailTrace_2021440
  have hstable : (prefixWord ++ tailWord_2021440).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2021440).length < 2 ^ (prefixWord ++ tailWord_2021440).sum := by decide
  have hdescent : baseEnd_2021440 < baseStart_2021440 := by decide
  rcases family_descends (prefixWord ++ tailWord_2021440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2021505 : List Nat := [1, 2, 4, 2, 3, 1, 2, 1, 5]
def baseStart_2021505 : Nat := 118140960795 + 2021505 * 2 ^ 59
def prefixEnd_2021505 : Nat := 4983230072969 + 3 ^ 40 * 2021505 * 2
def baseEnd_2021505 : Nat := 461334982429874927151455

theorem tailTrace_2021505 : CollatzResearch.WordTrace tailWord_2021505 prefixEnd_2021505 461334982429874927151455 := by
  unfold tailWord_2021505
  simp only [CollatzResearch.WordTrace]
  refine ⟨73730344541440105412705969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49153563027626736941803979 73730344541440105412705969)
  ·
    refine ⟨55297758406080079059529477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73730344541440105412705969 55297758406080079059529477)
    ·
      refine ⟨10368329701140014823661777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55297758406080079059529477 10368329701140014823661777)
      ·
        refine ⟨7776247275855011117746333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10368329701140014823661777 7776247275855011117746333)
        ·
          refine ⟨2916092728445629169154875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7776247275855011117746333 2916092728445629169154875)
          ·
            refine ⟨4374139092668443753732313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2916092728445629169154875 4374139092668443753732313)
            ·
              refine ⟨3280604319501332815299235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4374139092668443753732313 3280604319501332815299235)
              ·
                refine ⟨4920906479251999222948853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3280604319501332815299235 4920906479251999222948853)
                ·
                  refine ⟨461334982429874927151455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4920906479251999222948853 461334982429874927151455)
                  ·
                    rfl

theorem cell21_2021505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 2, 1, 5].length) (baseStart_2021505 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2021505 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2021505 prefixEnd_2021505 := by exact prefixLift 2021505
  have htrace : WordTrace (prefixWord ++ tailWord_2021505) baseStart_2021505 baseEnd_2021505 := by
    simpa [prefixWord, tailWord_2021505, baseEnd_2021505] using wordTrace_append hprefix tailTrace_2021505
  have hstable : (prefixWord ++ tailWord_2021505).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2021505).length < 2 ^ (prefixWord ++ tailWord_2021505).sum := by decide
  have hdescent : baseEnd_2021505 < baseStart_2021505 := by decide
  rcases family_descends (prefixWord ++ tailWord_2021505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2021533 : List Nat := [1, 4, 2, 1, 1, 4, 1, 7]
def baseStart_2021533 : Nat := 118140960795 + 2021533 * 2 ^ 59
def prefixEnd_2021533 : Nat := 4983230072969 + 3 ^ 40 * 2021533 * 2
def baseEnd_2021533 : Nat := 153780457470451033561577

theorem tailTrace_2021533 : CollatzResearch.WordTrace tailWord_2021533 prefixEnd_2021533 153780457470451033561577 := by
  unfold tailWord_2021533
  simp only [CollatzResearch.WordTrace]
  refine ⟨73731365785338666194725253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49154243856892444129816835 73731365785338666194725253)
  ·
    refine ⟨13824631084750999911510985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73731365785338666194725253 13824631084750999911510985)
    ·
      refine ⟨10368473313563249933633239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13824631084750999911510985 10368473313563249933633239)
      ·
        refine ⟨15552709970344874900449859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10368473313563249933633239 15552709970344874900449859)
        ·
          refine ⟨23329064955517312350674789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15552709970344874900449859 23329064955517312350674789)
          ·
            refine ⟨4374199679159496065751523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23329064955517312350674789 4374199679159496065751523)
            ·
              refine ⟨6561299518739244098627285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4374199679159496065751523 6561299518739244098627285)
              ·
                refine ⟨153780457470451033561577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6561299518739244098627285 153780457470451033561577)
                ·
                  rfl

theorem cell21_2021533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 1, 7].length) (baseStart_2021533 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2021533 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2021533 prefixEnd_2021533 := by exact prefixLift 2021533
  have htrace : WordTrace (prefixWord ++ tailWord_2021533) baseStart_2021533 baseEnd_2021533 := by
    simpa [prefixWord, tailWord_2021533, baseEnd_2021533] using wordTrace_append hprefix tailTrace_2021533
  have hstable : (prefixWord ++ tailWord_2021533).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2021533).length < 2 ^ (prefixWord ++ tailWord_2021533).sum := by decide
  have hdescent : baseEnd_2021533 < baseStart_2021533 := by decide
  rcases family_descends (prefixWord ++ tailWord_2021533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2021556 : List Nat := [2, 5, 3, 1, 1, 2, 1, 1, 5]
def baseStart_2021556 : Nat := 118140960795 + 2021556 * 2 ^ 59
def prefixEnd_2021556 : Nat := 4983230072969 + 3 ^ 40 * 2021556 * 2
def baseEnd_2021556 : Nat := 461346621324710171801351

theorem tailTrace_2021556 : CollatzResearch.WordTrace tailWord_2021556 prefixEnd_2021556 461346621324710171801351 := by
  unfold tailWord_2021556
  simp only [CollatzResearch.WordTrace]
  refine ⟨36866102332127670561406261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49154803109503560748541681 36866102332127670561406261)
  ·
    refine ⟨3456197093636969115131837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 36866102332127670561406261 3456197093636969115131837)
    ·
      refine ⟨1296073910113863418174439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3456197093636969115131837 1296073910113863418174439)
      ·
        refine ⟨1944110865170795127261659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1296073910113863418174439 1944110865170795127261659)
        ·
          refine ⟨2916166297756192690892489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1944110865170795127261659 2916166297756192690892489)
          ·
            refine ⟨2187124723317144518169367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2916166297756192690892489 2187124723317144518169367)
            ·
              refine ⟨3280687084975716777254051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2187124723317144518169367 3280687084975716777254051)
              ·
                refine ⟨4921030627463575165881077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3280687084975716777254051 4921030627463575165881077)
                ·
                  refine ⟨461346621324710171801351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4921030627463575165881077 461346621324710171801351)
                  ·
                    rfl

theorem cell21_2021556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 1, 1, 5].length) (baseStart_2021556 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2021556 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2021556 prefixEnd_2021556 := by exact prefixLift 2021556
  have htrace : WordTrace (prefixWord ++ tailWord_2021556) baseStart_2021556 baseEnd_2021556 := by
    simpa [prefixWord, tailWord_2021556, baseEnd_2021556] using wordTrace_append hprefix tailTrace_2021556
  have hstable : (prefixWord ++ tailWord_2021556).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2021556).length < 2 ^ (prefixWord ++ tailWord_2021556).sum := by decide
  have hdescent : baseEnd_2021556 < baseStart_2021556 := by decide
  rcases family_descends (prefixWord ++ tailWord_2021556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2021570 : List Nat := [3, 5, 1, 1, 1, 1, 4, 1, 4]
def baseStart_2021570 : Nat := 118140960795 + 2021570 * 2 ^ 59
def prefixEnd_2021570 : Nat := 4983230072969 + 3 ^ 40 * 2021570 * 2
def baseEnd_2021570 : Nat := 461349816315449258567989

theorem tailTrace_2021570 : CollatzResearch.WordTrace tailWord_2021570 prefixEnd_2021570 461349816315449258567989 := by
  unfold tailWord_2021570
  simp only [CollatzResearch.WordTrace]
  refine ⟨18433178821551155378455541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49155143524136414342548109 18433178821551155378455541)
  ·
    refine ⟨1728110514520420816730207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18433178821551155378455541 1728110514520420816730207)
    ·
      refine ⟨2592165771780631225095311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1728110514520420816730207 2592165771780631225095311)
      ·
        refine ⟨3888248657670946837642967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2592165771780631225095311 3888248657670946837642967)
        ·
          refine ⟨5832372986506420256464451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3888248657670946837642967 5832372986506420256464451)
          ·
            refine ⟨8748559479759630384696677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5832372986506420256464451 8748559479759630384696677)
            ·
              refine ⟨1640354902454930697130627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8748559479759630384696677 1640354902454930697130627)
              ·
                refine ⟨2460532353682396045695941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1640354902454930697130627 2460532353682396045695941)
                ·
                  refine ⟨461349816315449258567989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2460532353682396045695941 461349816315449258567989)
                  ·
                    rfl

theorem cell21_2021570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 4, 1, 4].length) (baseStart_2021570 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2021570 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2021570 prefixEnd_2021570 := by exact prefixLift 2021570
  have htrace : WordTrace (prefixWord ++ tailWord_2021570) baseStart_2021570 baseEnd_2021570 := by
    simpa [prefixWord, tailWord_2021570, baseEnd_2021570] using wordTrace_append hprefix tailTrace_2021570
  have hstable : (prefixWord ++ tailWord_2021570).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2021570).length < 2 ^ (prefixWord ++ tailWord_2021570).sum := by decide
  have hdescent : baseEnd_2021570 < baseStart_2021570 := by decide
  rcases family_descends (prefixWord ++ tailWord_2021570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2021640 : List Nat := [2, 1, 3, 2, 3, 2, 1, 2, 5]
def baseStart_2021640 : Nat := 118140960795 + 2021640 * 2 ^ 59
def prefixEnd_2021640 : Nat := 4983230072969 + 3 ^ 40 * 2021640 * 2
def baseEnd_2021640 : Nat := 461365791269144692401179

theorem tailTrace_2021640 : CollatzResearch.WordTrace tailWord_2021640 prefixEnd_2021640 461365791269144692401179 := by
  unfold tailWord_2021640
  simp only [CollatzResearch.WordTrace]
  refine ⟨36867634197975511734435187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49156845597300682312580249 36867634197975511734435187)
  ·
    refine ⟨55301451296963267601652781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36867634197975511734435187 55301451296963267601652781)
    ·
      refine ⟨20738044236361225350619793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55301451296963267601652781 20738044236361225350619793)
      ·
        refine ⟨15553533177270919012964845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20738044236361225350619793 15553533177270919012964845)
        ·
          refine ⟨5832574941476594629861817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15553533177270919012964845 5832574941476594629861817)
          ·
            refine ⟨4374431206107445972396363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5832574941476594629861817 4374431206107445972396363)
            ·
              refine ⟨6561646809161168958594545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4374431206107445972396363 6561646809161168958594545)
              ·
                refine ⟨4921235106870876718945909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6561646809161168958594545 4921235106870876718945909)
                ·
                  refine ⟨461365791269144692401179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4921235106870876718945909 461365791269144692401179)
                  ·
                    rfl

theorem cell21_2021640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 1, 2, 5].length) (baseStart_2021640 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2021640 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2021640 prefixEnd_2021640 := by exact prefixLift 2021640
  have htrace : WordTrace (prefixWord ++ tailWord_2021640) baseStart_2021640 baseEnd_2021640 := by
    simpa [prefixWord, tailWord_2021640, baseEnd_2021640] using wordTrace_append hprefix tailTrace_2021640
  have hstable : (prefixWord ++ tailWord_2021640).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2021640).length < 2 ^ (prefixWord ++ tailWord_2021640).sum := by decide
  have hdescent : baseEnd_2021640 < baseStart_2021640 := by decide
  rcases family_descends (prefixWord ++ tailWord_2021640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2021699 : List Nat := [1, 1, 1, 3, 1, 3, 4, 2, 5]
def baseStart_2021699 : Nat := 118140960795 + 2021699 * 2 ^ 59
def prefixEnd_2021699 : Nat := 4983230072969 + 3 ^ 40 * 2021699 * 2
def baseEnd_2021699 : Nat := 461379255872973700917725

theorem tailTrace_2021699 : CollatzResearch.WordTrace tailWord_2021699 prefixEnd_2021699 461379255872973700917725 := by
  unfold tailWord_2021699
  simp only [CollatzResearch.WordTrace]
  refine ⟨73737420302737276545268151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49158280201824851030178767 73737420302737276545268151)
  ·
    refine ⟨110606130454105914817902227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73737420302737276545268151 110606130454105914817902227)
    ·
      refine ⟨165909195681158872226853341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110606130454105914817902227 165909195681158872226853341)
      ·
        refine ⟨62215948380434577085070003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 165909195681158872226853341 62215948380434577085070003)
        ·
          refine ⟨93323922570651865627605005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62215948380434577085070003 93323922570651865627605005)
          ·
            refine ⟨34996470963994449610351877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93323922570651865627605005 34996470963994449610351877)
            ·
              refine ⟨6561838305748959301940977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34996470963994449610351877 6561838305748959301940977)
              ·
                refine ⟨4921378729311719476455733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6561838305748959301940977 4921378729311719476455733)
                ·
                  refine ⟨461379255872973700917725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4921378729311719476455733 461379255872973700917725)
                  ·
                    rfl

theorem cell21_2021699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 4, 2, 5].length) (baseStart_2021699 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2021699 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2021699 prefixEnd_2021699 := by exact prefixLift 2021699
  have htrace : WordTrace (prefixWord ++ tailWord_2021699) baseStart_2021699 baseEnd_2021699 := by
    simpa [prefixWord, tailWord_2021699, baseEnd_2021699] using wordTrace_append hprefix tailTrace_2021699
  have hstable : (prefixWord ++ tailWord_2021699).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2021699).length < 2 ^ (prefixWord ++ tailWord_2021699).sum := by decide
  have hdescent : baseEnd_2021699 < baseStart_2021699 := by decide
  rcases family_descends (prefixWord ++ tailWord_2021699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2021744 : List Nat := [2, 1, 1, 1, 4, 3, 1, 8]
def baseStart_2021744 : Nat := 118140960795 + 2021744 * 2 ^ 59
def prefixEnd_2021744 : Nat := 4983230072969 + 3 ^ 40 * 2021744 * 2
def baseEnd_2021744 : Nat := 153796508495354540889211

theorem tailTrace_2021744 : CollatzResearch.WordTrace tailWord_2021744 prefixEnd_2021744 153796508495354540889211 := by
  unfold tailWord_2021744
  simp only [CollatzResearch.WordTrace]
  refine ⟨36869530793787124615328143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49159374391716166153770857 36869530793787124615328143)
  ·
    refine ⟨55304296190680686922992215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36869530793787124615328143 55304296190680686922992215)
    ·
      refine ⟨82956444286021030384488323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55304296190680686922992215 82956444286021030384488323)
      ·
        refine ⟨124434666429031545576732485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82956444286021030384488323 124434666429031545576732485)
        ·
          refine ⟨23331499955443414795637341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 124434666429031545576732485 23331499955443414795637341)
          ·
            refine ⟨8749312483291280548364003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23331499955443414795637341 8749312483291280548364003)
            ·
              refine ⟨13123968724936920822546005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8749312483291280548364003 13123968724936920822546005)
              ·
                refine ⟨153796508495354540889211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13123968724936920822546005 153796508495354540889211)
                ·
                  rfl

theorem cell21_2021744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 8].length) (baseStart_2021744 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2021744 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2021744 prefixEnd_2021744 := by exact prefixLift 2021744
  have htrace : WordTrace (prefixWord ++ tailWord_2021744) baseStart_2021744 baseEnd_2021744 := by
    simpa [prefixWord, tailWord_2021744, baseEnd_2021744] using wordTrace_append hprefix tailTrace_2021744
  have hstable : (prefixWord ++ tailWord_2021744).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2021744).length < 2 ^ (prefixWord ++ tailWord_2021744).sum := by decide
  have hdescent : baseEnd_2021744 < baseStart_2021744 := by decide
  rcases family_descends (prefixWord ++ tailWord_2021744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2021761 : List Nat := [1, 2, 4, 3, 1, 1, 2, 7]
def baseStart_2021761 : Nat := 118140960795 + 2021761 * 2 ^ 59
def prefixEnd_2021761 : Nat := 4983230072969 + 3 ^ 40 * 2021761 * 2
def baseEnd_2021761 : Nat := 153797801705891790294755

theorem tailTrace_2021761 : CollatzResearch.WordTrace tailWord_2021761 prefixEnd_2021761 153797801705891790294755 := by
  unfold tailWord_2021761
  simp only [CollatzResearch.WordTrace]
  refine ⟨73739681628512661134025137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49159787752341774089350091 73739681628512661134025137)
  ·
    refine ⟨55304761221384495850518853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73739681628512661134025137 55304761221384495850518853)
    ·
      refine ⟨10369642729009592971972285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55304761221384495850518853 10369642729009592971972285)
      ·
        refine ⟨3888616023378597364489607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10369642729009592971972285 3888616023378597364489607)
        ·
          refine ⟨5832924035067896046734411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3888616023378597364489607 5832924035067896046734411)
          ·
            refine ⟨8749386052601844070101617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5832924035067896046734411 8749386052601844070101617)
            ·
              refine ⟨6562039539451383052576213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8749386052601844070101617 6562039539451383052576213)
              ·
                refine ⟨153797801705891790294755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6562039539451383052576213 153797801705891790294755)
                ·
                  rfl

theorem cell21_2021761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 2, 7].length) (baseStart_2021761 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2021761 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2021761 prefixEnd_2021761 := by exact prefixLift 2021761
  have htrace : WordTrace (prefixWord ++ tailWord_2021761) baseStart_2021761 baseEnd_2021761 := by
    simpa [prefixWord, tailWord_2021761, baseEnd_2021761] using wordTrace_append hprefix tailTrace_2021761
  have hstable : (prefixWord ++ tailWord_2021761).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2021761).length < 2 ^ (prefixWord ++ tailWord_2021761).sum := by decide
  have hdescent : baseEnd_2021761 < baseStart_2021761 := by decide
  rcases family_descends (prefixWord ++ tailWord_2021761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2021812 : List Nat := [2, 5, 2, 2, 1, 1, 3, 5]
def baseStart_2021812 : Nat := 118140960795 + 2021812 * 2 ^ 59
def prefixEnd_2021812 : Nat := 4983230072969 + 3 ^ 40 * 2021812 * 2
def baseEnd_2021812 : Nat := 153801681337503538511387

theorem tailTrace_2021812 : CollatzResearch.WordTrace tailWord_2021812 prefixEnd_2021812 153801681337503538511387 := by
  unfold tailWord_2021812
  simp only [CollatzResearch.WordTrace]
  refine ⟨36870770875663948422065845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49161027834218597896087793 36870770875663948422065845)
  ·
    refine ⟨3456634769593495164568673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 36870770875663948422065845 3456634769593495164568673)
    ·
      refine ⟨2592476077195121373426505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3456634769593495164568673 2592476077195121373426505)
      ·
        refine ⟨1944357057896341030069879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2592476077195121373426505 1944357057896341030069879)
        ·
          refine ⟨2916535586844511545104819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1944357057896341030069879 2916535586844511545104819)
          ·
            refine ⟨4374803380266767317657229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2916535586844511545104819 4374803380266767317657229)
            ·
              refine ⟨1640551267600037744121461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4374803380266767317657229 1640551267600037744121461)
              ·
                refine ⟨153801681337503538511387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1640551267600037744121461 153801681337503538511387)
                ·
                  rfl

theorem cell21_2021812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 3, 5].length) (baseStart_2021812 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2021812 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2021812 prefixEnd_2021812 := by exact prefixLift 2021812
  have htrace : WordTrace (prefixWord ++ tailWord_2021812) baseStart_2021812 baseEnd_2021812 := by
    simpa [prefixWord, tailWord_2021812, baseEnd_2021812] using wordTrace_append hprefix tailTrace_2021812
  have hstable : (prefixWord ++ tailWord_2021812).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2021812).length < 2 ^ (prefixWord ++ tailWord_2021812).sum := by decide
  have hdescent : baseEnd_2021812 < baseStart_2021812 := by decide
  rcases family_descends (prefixWord ++ tailWord_2021812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2021902 : List Nat := [4, 1, 1, 2, 3, 2, 3, 2, 3]
def baseStart_2021902 : Nat := 118140960795 + 2021902 * 2 ^ 59
def prefixEnd_2021902 : Nat := 4983230072969 + 3 ^ 40 * 2021902 * 2
def baseEnd_2021902 : Nat := 461425583238690459033977

theorem tailTrace_2021902 : CollatzResearch.WordTrace tailWord_2021902 prefixEnd_2021902 461425583238690459033977 := by
  unfold tailWord_2021902
  simp only [CollatzResearch.WordTrace]
  refine ⟨9218103040125230276863495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49163216214001228143271973 9218103040125230276863495)
  ·
    refine ⟨13827154560187845415295243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9218103040125230276863495 13827154560187845415295243)
    ·
      refine ⟨20740731840281768122942865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13827154560187845415295243 20740731840281768122942865)
      ·
        refine ⟨15555548880211326092207149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20740731840281768122942865 15555548880211326092207149)
        ·
          refine ⟨5833330830079247284577681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15555548880211326092207149 5833330830079247284577681)
          ·
            refine ⟨4374998122559435463433261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5833330830079247284577681 4374998122559435463433261)
            ·
              refine ⟨1640624295959788298787473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4374998122559435463433261 1640624295959788298787473)
              ·
                refine ⟨1230468221969841224090605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1640624295959788298787473 1230468221969841224090605)
                ·
                  refine ⟨461425583238690459033977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1230468221969841224090605 461425583238690459033977)
                  ·
                    rfl

theorem cell21_2021902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 3, 2, 3].length) (baseStart_2021902 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2021902 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2021902 prefixEnd_2021902 := by exact prefixLift 2021902
  have htrace : WordTrace (prefixWord ++ tailWord_2021902) baseStart_2021902 baseEnd_2021902 := by
    simpa [prefixWord, tailWord_2021902, baseEnd_2021902] using wordTrace_append hprefix tailTrace_2021902
  have hstable : (prefixWord ++ tailWord_2021902).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2021902).length < 2 ^ (prefixWord ++ tailWord_2021902).sum := by decide
  have hdescent : baseEnd_2021902 < baseStart_2021902 := by decide
  rcases family_descends (prefixWord ++ tailWord_2021902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2021916 : List Nat := [2, 2, 3, 1, 2, 4, 2, 1, 4]
def baseStart_2021916 : Nat := 118140960795 + 2021916 * 2 ^ 59
def prefixEnd_2021916 : Nat := 4983230072969 + 3 ^ 40 * 2021916 * 2
def baseEnd_2021916 : Nat := 461428778229429545800615

theorem tailTrace_2021916 : CollatzResearch.WordTrace tailWord_2021916 prefixEnd_2021916 461428778229429545800615 := by
  unfold tailWord_2021916
  simp only [CollatzResearch.WordTrace]
  refine ⟨36872667471475561302958801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49163556628634081737278401 36872667471475561302958801)
  ·
    refine ⟨27654500603606670977219101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36872667471475561302958801 27654500603606670977219101)
    ·
      refine ⟨10370437726352501616457163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27654500603606670977219101 10370437726352501616457163)
      ·
        refine ⟨15555656589528752424685745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10370437726352501616457163 15555656589528752424685745)
        ·
          refine ⟨11666742442146564318514309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15555656589528752424685745 11666742442146564318514309)
          ·
            refine ⟨2187514207902480809721433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11666742442146564318514309 2187514207902480809721433)
            ·
              refine ⟨1640635655926860607291075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2187514207902480809721433 1640635655926860607291075)
              ·
                refine ⟨2460953483890290910936613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1640635655926860607291075 2460953483890290910936613)
                ·
                  refine ⟨461428778229429545800615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2460953483890290910936613 461428778229429545800615)
                  ·
                    rfl

theorem cell21_2021916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 2, 1, 4].length) (baseStart_2021916 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2021916 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2021916 prefixEnd_2021916 := by exact prefixLift 2021916
  have htrace : WordTrace (prefixWord ++ tailWord_2021916) baseStart_2021916 baseEnd_2021916 := by
    simpa [prefixWord, tailWord_2021916, baseEnd_2021916] using wordTrace_append hprefix tailTrace_2021916
  have hstable : (prefixWord ++ tailWord_2021916).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2021916).length < 2 ^ (prefixWord ++ tailWord_2021916).sum := by decide
  have hdescent : baseEnd_2021916 < baseStart_2021916 := by decide
  rcases family_descends (prefixWord ++ tailWord_2021916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2021944 : List Nat := [2, 1, 2, 1, 4, 1, 2, 5, 3]
def baseStart_2021944 : Nat := 118140960795 + 2021944 * 2 ^ 59
def prefixEnd_2021944 : Nat := 4983230072969 + 3 ^ 40 * 2021944 * 2
def baseEnd_2021944 : Nat := 461435168210907719333891

theorem tailTrace_2021944 : CollatzResearch.WordTrace tailWord_2021944 prefixEnd_2021944 461435168210907719333891 := by
  unfold tailWord_2021944
  simp only [CollatzResearch.WordTrace]
  refine ⟨36873178093424841693968443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49164237457899788925291257 36873178093424841693968443)
  ·
    refine ⟨55309767140137262540952665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36873178093424841693968443 55309767140137262540952665)
    ·
      refine ⟨41482325355102946905714499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55309767140137262540952665 41482325355102946905714499)
      ·
        refine ⟨62223488032654420358571749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41482325355102946905714499 62223488032654420358571749)
        ·
          refine ⟨11666904006122703817232203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62223488032654420358571749 11666904006122703817232203)
          ·
            refine ⟨17500356009184055725848305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11666904006122703817232203 17500356009184055725848305)
            ·
              refine ⟨13125267006888041794386229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17500356009184055725848305 13125267006888041794386229)
              ·
                refine ⟨1230493781895753918223709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13125267006888041794386229 1230493781895753918223709)
                ·
                  refine ⟨461435168210907719333891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1230493781895753918223709 461435168210907719333891)
                  ·
                    rfl

theorem cell21_2021944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 5, 3].length) (baseStart_2021944 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2021944 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2021944 prefixEnd_2021944 := by exact prefixLift 2021944
  have htrace : WordTrace (prefixWord ++ tailWord_2021944) baseStart_2021944 baseEnd_2021944 := by
    simpa [prefixWord, tailWord_2021944, baseEnd_2021944] using wordTrace_append hprefix tailTrace_2021944
  have hstable : (prefixWord ++ tailWord_2021944).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2021944).length < 2 ^ (prefixWord ++ tailWord_2021944).sum := by decide
  have hdescent : baseEnd_2021944 < baseStart_2021944 := by decide
  rcases family_descends (prefixWord ++ tailWord_2021944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2022020 : List Nat := [2, 3, 2, 1, 3, 2, 2, 1, 5]
def baseStart_2022020 : Nat := 118140960795 + 2022020 * 2 ^ 59
def prefixEnd_2022020 : Nat := 4983230072969 + 3 ^ 40 * 2022020 * 2
def baseEnd_2022020 : Nat := 461452512446348476067069

theorem tailTrace_2022020 : CollatzResearch.WordTrace tailWord_2022020 prefixEnd_2022020 461452512446348476067069 := by
  unfold tailWord_2022020
  simp only [CollatzResearch.WordTrace]
  refine ⟨36874564067287174183851757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49166085423049565578469009 36874564067287174183851757)
  ·
    refine ⟨13827961525232690318944409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36874564067287174183851757 13827961525232690318944409)
    ·
      refine ⟨10370971143924517739208307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13827961525232690318944409 10370971143924517739208307)
      ·
        refine ⟨15556456715886776608812461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10370971143924517739208307 15556456715886776608812461)
        ·
          refine ⟨5833671268457541228304673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15556456715886776608812461 5833671268457541228304673)
          ·
            refine ⟨4375253451343155921228505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5833671268457541228304673 4375253451343155921228505)
            ·
              refine ⟨3281440088507366940921379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4375253451343155921228505 3281440088507366940921379)
              ·
                refine ⟨4922160132761050411382069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3281440088507366940921379 4922160132761050411382069)
                ·
                  refine ⟨461452512446348476067069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4922160132761050411382069 461452512446348476067069)
                  ·
                    rfl

theorem cell21_2022020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 2, 1, 5].length) (baseStart_2022020 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2022020 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2022020 prefixEnd_2022020 := by exact prefixLift 2022020
  have htrace : WordTrace (prefixWord ++ tailWord_2022020) baseStart_2022020 baseEnd_2022020 := by
    simpa [prefixWord, tailWord_2022020, baseEnd_2022020] using wordTrace_append hprefix tailTrace_2022020
  have hstable : (prefixWord ++ tailWord_2022020).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2022020).length < 2 ^ (prefixWord ++ tailWord_2022020).sum := by decide
  have hdescent : baseEnd_2022020 < baseStart_2022020 := by decide
  rcases family_descends (prefixWord ++ tailWord_2022020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2022079 : List Nat := [1, 1, 2, 2, 2, 4, 3, 1, 5]
def baseStart_2022079 : Nat := 118140960795 + 2022079 * 2 ^ 59
def prefixEnd_2022079 : Nat := 4983230072969 + 3 ^ 40 * 2022079 * 2
def baseEnd_2022079 : Nat := 461465977050177484583615

theorem tailTrace_2022079 : CollatzResearch.WordTrace tailWord_2022079 prefixEnd_2022079 461465977050177484583615 := by
  unfold tailWord_2022079
  simp only [CollatzResearch.WordTrace]
  refine ⟨73751280041360601444101291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49167520027573734296067527 73751280041360601444101291)
  ·
    refine ⟨110626920062040902166151937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73751280041360601444101291 110626920062040902166151937)
    ·
      refine ⟨82970190046530676624613953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110626920062040902166151937 82970190046530676624613953)
      ·
        refine ⟨62227642534898007468460465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82970190046530676624613953 62227642534898007468460465)
        ·
          refine ⟨46670731901173505601345349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62227642534898007468460465 46670731901173505601345349)
          ·
            refine ⟨8750762231470032300252253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46670731901173505601345349 8750762231470032300252253)
            ·
              refine ⟨3281535836801262112594595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8750762231470032300252253 3281535836801262112594595)
              ·
                refine ⟨4922303755201893168891893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3281535836801262112594595 4922303755201893168891893)
                ·
                  refine ⟨461465977050177484583615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4922303755201893168891893 461465977050177484583615)
                  ·
                    rfl

theorem cell21_2022079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 3, 1, 5].length) (baseStart_2022079 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2022079 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2022079 prefixEnd_2022079 := by exact prefixLift 2022079
  have htrace : WordTrace (prefixWord ++ tailWord_2022079) baseStart_2022079 baseEnd_2022079 := by
    simpa [prefixWord, tailWord_2022079, baseEnd_2022079] using wordTrace_append hprefix tailTrace_2022079
  have hstable : (prefixWord ++ tailWord_2022079).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2022079).length < 2 ^ (prefixWord ++ tailWord_2022079).sum := by decide
  have hdescent : baseEnd_2022079 < baseStart_2022079 := by decide
  rcases family_descends (prefixWord ++ tailWord_2022079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2022130 : List Nat := [3, 2, 1, 3, 1, 4, 2, 2, 3]
def baseStart_2022130 : Nat := 118140960795 + 2022130 * 2 ^ 59
def prefixEnd_2022130 : Nat := 4983230072969 + 3 ^ 40 * 2022130 * 2
def baseEnd_2022130 : Nat := 461477615945012729233511

theorem tailTrace_2022130 : CollatzResearch.WordTrace tailWord_2022130 prefixEnd_2022130 461477615945012729233511 := by
  unfold tailWord_2022130
  simp only [CollatzResearch.WordTrace]
  refine ⟨18438285041043959288551961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49168760109450558102805229 18438285041043959288551961)
  ·
    refine ⟨13828713780782969466413971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18438285041043959288551961 13828713780782969466413971)
    ·
      refine ⟨20743070671174454199620957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13828713780782969466413971 20743070671174454199620957)
      ·
        refine ⟨7778651501690420324857859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20743070671174454199620957 7778651501690420324857859)
        ·
          refine ⟨11667977252535630487286789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7778651501690420324857859 11667977252535630487286789)
          ·
            refine ⟨2187745734850430716366273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11667977252535630487286789 2187745734850430716366273)
            ·
              refine ⟨1640809301137823037274705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2187745734850430716366273 1640809301137823037274705)
              ·
                refine ⟨1230606975853367277956029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1640809301137823037274705 1230606975853367277956029)
                ·
                  refine ⟨461477615945012729233511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1230606975853367277956029 461477615945012729233511)
                  ·
                    rfl

theorem cell21_2022130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 2, 2, 3].length) (baseStart_2022130 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2022130 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2022130 prefixEnd_2022130 := by exact prefixLift 2022130
  have htrace : WordTrace (prefixWord ++ tailWord_2022130) baseStart_2022130 baseEnd_2022130 := by
    simpa [prefixWord, tailWord_2022130, baseEnd_2022130] using wordTrace_append hprefix tailTrace_2022130
  have hstable : (prefixWord ++ tailWord_2022130).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2022130).length < 2 ^ (prefixWord ++ tailWord_2022130).sum := by decide
  have hdescent : baseEnd_2022130 < baseStart_2022130 := by decide
  rcases family_descends (prefixWord ++ tailWord_2022130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2022172 : List Nat := [2, 2, 3, 1, 1, 3, 1, 5, 3]
def baseStart_2022172 : Nat := 118140960795 + 2022172 * 2 ^ 59
def prefixEnd_2022172 : Nat := 4983230072969 + 3 ^ 40 * 2022172 * 2
def baseEnd_2022172 : Nat := 461487200917229989533425

theorem tailTrace_2022172 : CollatzResearch.WordTrace tailWord_2022172 prefixEnd_2022172 461487200917229989533425 := by
  unfold tailWord_2022172
  simp only [CollatzResearch.WordTrace]
  refine ⟨36877336015011839163618385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49169781353349118884824513 36877336015011839163618385)
  ·
    refine ⟨27658002011258879372713789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36877336015011839163618385 27658002011258879372713789)
    ·
      refine ⟨10371750754222079764767671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27658002011258879372713789 10371750754222079764767671)
      ·
        refine ⟨15557626131333119647151507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10371750754222079764767671 15557626131333119647151507)
        ·
          refine ⟨23336439196999679470727261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15557626131333119647151507 23336439196999679470727261)
          ·
            refine ⟨8751164698874879801522723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23336439196999679470727261 8751164698874879801522723)
            ·
              refine ⟨13126747048312319702284085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8751164698874879801522723 13126747048312319702284085)
              ·
                refine ⟨1230632535779279972089133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13126747048312319702284085 1230632535779279972089133)
                ·
                  refine ⟨461487200917229989533425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1230632535779279972089133 461487200917229989533425)
                  ·
                    rfl

theorem cell21_2022172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 5, 3].length) (baseStart_2022172 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2022172 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2022172 prefixEnd_2022172 := by exact prefixLift 2022172
  have htrace : WordTrace (prefixWord ++ tailWord_2022172) baseStart_2022172 baseEnd_2022172 := by
    simpa [prefixWord, tailWord_2022172, baseEnd_2022172] using wordTrace_append hprefix tailTrace_2022172
  have hstable : (prefixWord ++ tailWord_2022172).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2022172).length < 2 ^ (prefixWord ++ tailWord_2022172).sum := by decide
  have hdescent : baseEnd_2022172 < baseStart_2022172 := by decide
  rcases family_descends (prefixWord ++ tailWord_2022172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2022217 : List Nat := [1, 2, 1, 1, 2, 7, 2, 5]
def baseStart_2022217 : Nat := 118140960795 + 2022217 * 2 ^ 59
def prefixEnd_2022217 : Nat := 4983230072969 + 3 ^ 40 * 2022217 * 2
def baseEnd_2022217 : Nat := 153832490176773303761111

theorem tailTrace_2022217 : CollatzResearch.WordTrace tailWord_2022217 prefixEnd_2022217 153832490176773303761111 := by
  unfold tailWord_2022217
  simp only [CollatzResearch.WordTrace]
  refine ⟨73756313314860651012624905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49170875543240434008416603 73756313314860651012624905)
  ·
    refine ⟨55317234986145488259468679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73756313314860651012624905 55317234986145488259468679)
    ·
      refine ⟨82975852479218232389203019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55317234986145488259468679 82975852479218232389203019)
      ·
        refine ⟨124463778718827348583804529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82975852479218232389203019 124463778718827348583804529)
        ·
          refine ⟨93347834039120511437853397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124463778718827348583804529 93347834039120511437853397)
          ·
            refine ⟨2187839860291886986824689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 93347834039120511437853397 2187839860291886986824689)
            ·
              refine ⟨1640879895218915240118517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2187839860291886986824689 1640879895218915240118517)
              ·
                refine ⟨153832490176773303761111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1640879895218915240118517 153832490176773303761111)
                ·
                  rfl

theorem cell21_2022217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 2, 5].length) (baseStart_2022217 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2022217 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2022217 prefixEnd_2022217 := by exact prefixLift 2022217
  have htrace : WordTrace (prefixWord ++ tailWord_2022217) baseStart_2022217 baseEnd_2022217 := by
    simpa [prefixWord, tailWord_2022217, baseEnd_2022217] using wordTrace_append hprefix tailTrace_2022217
  have hstable : (prefixWord ++ tailWord_2022217).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2022217).length < 2 ^ (prefixWord ++ tailWord_2022217).sum := by decide
  have hdescent : baseEnd_2022217 < baseStart_2022217 := by decide
  rcases family_descends (prefixWord ++ tailWord_2022217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2022245 : List Nat := [1, 3, 1, 3, 1, 1, 4, 1, 6]
def baseStart_2022245 : Nat := 118140960795 + 2022245 * 2 ^ 59
def prefixEnd_2022245 : Nat := 4983230072969 + 3 ^ 40 * 2022245 * 2
def baseEnd_2022245 : Nat := 461503860511798084816609

theorem tailTrace_2022245 : CollatzResearch.WordTrace tailWord_2022245 prefixEnd_2022245 461503860511798084816609 := by
  unfold tailWord_2022245
  simp only [CollatzResearch.WordTrace]
  refine ⟨73757334558759211794644189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49171556372506141196429459 73757334558759211794644189)
  ·
    refine ⟨27659000459534704422991571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73757334558759211794644189 27659000459534704422991571)
    ·
      refine ⟨41488500689302056634487357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27659000459534704422991571 41488500689302056634487357)
      ·
        refine ⟨15558187758488271237932759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41488500689302056634487357 15558187758488271237932759)
        ·
          refine ⟨23337281637732406856899139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15558187758488271237932759 23337281637732406856899139)
          ·
            refine ⟨35005922456598610285348709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23337281637732406856899139 35005922456598610285348709)
            ·
              refine ⟨6563610460612239428502883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35005922456598610285348709 6563610460612239428502883)
              ·
                refine ⟨9845415690918359142754325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6563610460612239428502883 9845415690918359142754325)
                ·
                  refine ⟨461503860511798084816609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9845415690918359142754325 461503860511798084816609)
                  ·
                    rfl

theorem cell21_2022245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 4, 1, 6].length) (baseStart_2022245 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2022245 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2022245 prefixEnd_2022245 := by exact prefixLift 2022245
  have htrace : WordTrace (prefixWord ++ tailWord_2022245) baseStart_2022245 baseEnd_2022245 := by
    simpa [prefixWord, tailWord_2022245, baseEnd_2022245] using wordTrace_append hprefix tailTrace_2022245
  have hstable : (prefixWord ++ tailWord_2022245).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2022245).length < 2 ^ (prefixWord ++ tailWord_2022245).sum := by decide
  have hdescent : baseEnd_2022245 < baseStart_2022245 := by decide
  rcases family_descends (prefixWord ++ tailWord_2022245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2022248 : List Nat := [2, 1, 4, 2, 1, 4, 1, 1, 5]
def baseStart_2022248 : Nat := 118140960795 + 2022248 * 2 ^ 59
def prefixEnd_2022248 : Nat := 4983230072969 + 3 ^ 40 * 2022248 * 2
def baseEnd_2022248 : Nat := 461504545152670746266603

theorem tailTrace_2022248 : CollatzResearch.WordTrace tailWord_2022248 prefixEnd_2022248 461504545152670746266603 := by
  unfold tailWord_2022248
  simp only [CollatzResearch.WordTrace]
  refine ⟨36878721988874171653501699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49171629318498895538002265 36878721988874171653501699)
  ·
    refine ⟨55318082983311257480252549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36878721988874171653501699 55318082983311257480252549)
    ·
      refine ⟨10372140559370860777547353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55318082983311257480252549 10372140559370860777547353)
      ·
        refine ⟨7779105419528145583160515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10372140559370860777547353 7779105419528145583160515)
        ·
          refine ⟨11668658129292218374740773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7779105419528145583160515 11668658129292218374740773)
          ·
            refine ⟨2187873399242290945263895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11668658129292218374740773 2187873399242290945263895)
            ·
              refine ⟨3281810098863436417895843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2187873399242290945263895 3281810098863436417895843)
              ·
                refine ⟨4922715148295154626843765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3281810098863436417895843 4922715148295154626843765)
                ·
                  refine ⟨461504545152670746266603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4922715148295154626843765 461504545152670746266603)
                  ·
                    rfl

theorem cell21_2022248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 1, 1, 5].length) (baseStart_2022248 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2022248 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2022248 prefixEnd_2022248 := by exact prefixLift 2022248
  have htrace : WordTrace (prefixWord ++ tailWord_2022248) baseStart_2022248 baseEnd_2022248 := by
    simpa [prefixWord, tailWord_2022248, baseEnd_2022248] using wordTrace_append hprefix tailTrace_2022248
  have hstable : (prefixWord ++ tailWord_2022248).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2022248).length < 2 ^ (prefixWord ++ tailWord_2022248).sum := by decide
  have hdescent : baseEnd_2022248 < baseStart_2022248 := by decide
  rcases family_descends (prefixWord ++ tailWord_2022248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2022259 : List Nat := [1, 1, 1, 2, 2, 1, 5, 8]
def baseStart_2022259 : Nat := 118140960795 + 2022259 * 2 ^ 59
def prefixEnd_2022259 : Nat := 4983230072969 + 3 ^ 40 * 2022259 * 2
def baseEnd_2022259 : Nat := 153835685167512390527749

theorem tailTrace_2022259 : CollatzResearch.WordTrace tailWord_2022259 prefixEnd_2022259 153835685167512390527749 := by
  unfold tailWord_2022259
  simp only [CollatzResearch.WordTrace]
  refine ⟨73757845180708492185653831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49171896787138994790435887 73757845180708492185653831)
  ·
    refine ⟨110636767771062738278480747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73757845180708492185653831 110636767771062738278480747)
    ·
      refine ⟨165955151656594107417721121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110636767771062738278480747 165955151656594107417721121)
      ·
        refine ⟨124466363742445580563290841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165955151656594107417721121 124466363742445580563290841)
        ·
          refine ⟨93349772806834185422468131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124466363742445580563290841 93349772806834185422468131)
          ·
            refine ⟨140024659210251278133702197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93349772806834185422468131 140024659210251278133702197)
            ·
              refine ⟨13127311800961057325034581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 140024659210251278133702197 13127311800961057325034581)
              ·
                refine ⟨153835685167512390527749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13127311800961057325034581 153835685167512390527749)
                ·
                  rfl

theorem cell21_2022259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 8].length) (baseStart_2022259 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2022259 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2022259 prefixEnd_2022259 := by exact prefixLift 2022259
  have htrace : WordTrace (prefixWord ++ tailWord_2022259) baseStart_2022259 baseEnd_2022259 := by
    simpa [prefixWord, tailWord_2022259, baseEnd_2022259] using wordTrace_append hprefix tailTrace_2022259
  have hstable : (prefixWord ++ tailWord_2022259).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2022259).length < 2 ^ (prefixWord ++ tailWord_2022259).sum := by decide
  have hdescent : baseEnd_2022259 < baseStart_2022259 := by decide
  rcases family_descends (prefixWord ++ tailWord_2022259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2022324 : List Nat := [2, 5, 2, 1, 1, 1, 1, 1, 7]
def baseStart_2022324 : Nat := 118140960795 + 2022324 * 2 ^ 59
def prefixEnd_2022324 : Nat := 4983230072969 + 3 ^ 40 * 2022324 * 2
def baseEnd_2022324 : Nat := 461521889388111502999781

theorem tailTrace_2022324 : CollatzResearch.WordTrace tailWord_2022324 prefixEnd_2022324 461521889388111502999781 := by
  unfold tailWord_2022324
  simp only [CollatzResearch.WordTrace]
  refine ⟨36880107962736504143385013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49173477283648672191180017 36880107962736504143385013)
  ·
    refine ⟨3457510121506547263442345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 36880107962736504143385013 3457510121506547263442345)
    ·
      refine ⟨2593132591129910447581759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3457510121506547263442345 2593132591129910447581759)
      ·
        refine ⟨3889698886694865671372639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2593132591129910447581759 3889698886694865671372639)
        ·
          refine ⟨5834548330042298507058959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3889698886694865671372639 5834548330042298507058959)
          ·
            refine ⟨8751822495063447760588439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5834548330042298507058959 8751822495063447760588439)
            ·
              refine ⟨13127733742595171640882659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8751822495063447760588439 13127733742595171640882659)
              ·
                refine ⟨19691600613892757461323989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13127733742595171640882659 19691600613892757461323989)
                ·
                  refine ⟨461521889388111502999781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19691600613892757461323989 461521889388111502999781)
                  ·
                    rfl

theorem cell21_2022324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 1, 7].length) (baseStart_2022324 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2022324 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2022324 prefixEnd_2022324 := by exact prefixLift 2022324
  have htrace : WordTrace (prefixWord ++ tailWord_2022324) baseStart_2022324 baseEnd_2022324 := by
    simpa [prefixWord, tailWord_2022324, baseEnd_2022324] using wordTrace_append hprefix tailTrace_2022324
  have hstable : (prefixWord ++ tailWord_2022324).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2022324).length < 2 ^ (prefixWord ++ tailWord_2022324).sum := by decide
  have hdescent : baseEnd_2022324 < baseStart_2022324 := by decide
  rcases family_descends (prefixWord ++ tailWord_2022324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2022411 : List Nat := [1, 1, 1, 1, 6, 2, 9]
def baseStart_2022411 : Nat := 118140960795 + 2022411 * 2 ^ 59
def prefixEnd_2022411 : Nat := 4983230072969 + 3 ^ 40 * 2022411 * 2
def baseEnd_2022411 : Nat := 51282415997046520561067

theorem tailTrace_2022411 : CollatzResearch.WordTrace tailWord_2022411 prefixEnd_2022411 51282415997046520561067 := by
  unfold tailWord_2022411
  simp only [CollatzResearch.WordTrace]
  refine ⟨73763389076157822145187087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49175592717438548096791391 73763389076157822145187087)
  ·
    refine ⟨110645083614236733217780631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73763389076157822145187087 110645083614236733217780631)
    ·
      refine ⟨165967625421355099826670947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110645083614236733217780631 165967625421355099826670947)
      ·
        refine ⟨248951438132032649740006421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165967625421355099826670947 248951438132032649740006421)
        ·
          refine ⟨11669598662439030456562801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 248951438132032649740006421 11669598662439030456562801)
          ·
            refine ⟨8752198996829272842422101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11669598662439030456562801 8752198996829272842422101)
            ·
              refine ⟨51282415997046520561067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8752198996829272842422101 51282415997046520561067)
              ·
                rfl

theorem cell21_2022411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 9].length) (baseStart_2022411 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2022411 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2022411 prefixEnd_2022411 := by exact prefixLift 2022411
  have htrace : WordTrace (prefixWord ++ tailWord_2022411) baseStart_2022411 baseEnd_2022411 := by
    simpa [prefixWord, tailWord_2022411, baseEnd_2022411] using wordTrace_append hprefix tailTrace_2022411
  have hstable : (prefixWord ++ tailWord_2022411).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2022411).length < 2 ^ (prefixWord ++ tailWord_2022411).sum := by decide
  have hdescent : baseEnd_2022411 < baseStart_2022411 := by decide
  rcases family_descends (prefixWord ++ tailWord_2022411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2022431 : List Nat := [1, 1, 2, 4, 1, 5, 2, 1, 4]
def baseStart_2022431 : Nat := 118140960795 + 2022431 * 2 ^ 59
def prefixEnd_2022431 : Nat := 4983230072969 + 3 ^ 40 * 2022431 * 2
def baseEnd_2022431 : Nat := 461546308245903094716229

theorem tailTrace_2022431 : CollatzResearch.WordTrace tailWord_2022431 prefixEnd_2022431 461546308245903094716229 := by
  unfold tailWord_2022431
  simp only [CollatzResearch.WordTrace]
  refine ⟨73764118536085365560915147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49176079024056910373943431 73764118536085365560915147)
  ·
    refine ⟨110646177804128048341372721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73764118536085365560915147 110646177804128048341372721)
    ·
      refine ⟨82984633353096036256029541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110646177804128048341372721 82984633353096036256029541)
      ·
        refine ⟨15559618753705506798005539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82984633353096036256029541 15559618753705506798005539)
        ·
          refine ⟨23339428130558260197008309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15559618753705506798005539 23339428130558260197008309)
          ·
            refine ⟨2188071387239836893469529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23339428130558260197008309 2188071387239836893469529)
            ·
              refine ⟨1641053540429877670102147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2188071387239836893469529 1641053540429877670102147)
              ·
                refine ⟨2461580310644816505153221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1641053540429877670102147 2461580310644816505153221)
                ·
                  refine ⟨461546308245903094716229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2461580310644816505153221 461546308245903094716229)
                  ·
                    rfl

theorem cell21_2022431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 2, 1, 4].length) (baseStart_2022431 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2022431 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2022431 prefixEnd_2022431 := by exact prefixLift 2022431
  have htrace : WordTrace (prefixWord ++ tailWord_2022431) baseStart_2022431 baseEnd_2022431 := by
    simpa [prefixWord, tailWord_2022431, baseEnd_2022431] using wordTrace_append hprefix tailTrace_2022431
  have hstable : (prefixWord ++ tailWord_2022431).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2022431).length < 2 ^ (prefixWord ++ tailWord_2022431).sum := by decide
  have hdescent : baseEnd_2022431 < baseStart_2022431 := by decide
  rcases family_descends (prefixWord ++ tailWord_2022431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2022639 : List Nat := [1, 1, 2, 1, 7, 9]
def baseStart_2022639 : Nat := 118140960795 + 2022639 * 2 ^ 59
def prefixEnd_2022639 : Nat := 4983230072969 + 3 ^ 40 * 2022639 * 2
def baseEnd_2022639 : Nat := 17096065802953368712931

theorem tailTrace_2022639 : CollatzResearch.WordTrace tailWord_2022639 prefixEnd_2022639 17096065802953368712931 := by
  unfold tailWord_2022639
  simp only [CollatzResearch.WordTrace]
  refine ⟨73771704919331817084486971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49181136612887878056324647 73771704919331817084486971)
  ·
    refine ⟨110657557378997725626730457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73771704919331817084486971 110657557378997725626730457)
    ·
      refine ⟨82993168034248294220047843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110657557378997725626730457 82993168034248294220047843)
      ·
        refine ⟨124489752051372441330071765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82993168034248294220047843 124489752051372441330071765)
        ·
          refine ⟨2917728563704041593673557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 124489752051372441330071765 2917728563704041593673557)
          ·
            refine ⟨17096065802953368712931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2917728563704041593673557 17096065802953368712931)
            ·
              rfl

theorem cell21_2022639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 9].length) (baseStart_2022639 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2022639 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2022639 prefixEnd_2022639 := by exact prefixLift 2022639
  have htrace : WordTrace (prefixWord ++ tailWord_2022639) baseStart_2022639 baseEnd_2022639 := by
    simpa [prefixWord, tailWord_2022639, baseEnd_2022639] using wordTrace_append hprefix tailTrace_2022639
  have hstable : (prefixWord ++ tailWord_2022639).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2022639).length < 2 ^ (prefixWord ++ tailWord_2022639).sum := by decide
  have hdescent : baseEnd_2022639 < baseStart_2022639 := by decide
  rcases family_descends (prefixWord ++ tailWord_2022639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2022670 : List Nat := [4, 1, 1, 2, 1, 3, 1, 1, 7]
def baseStart_2022670 : Nat := 118140960795 + 2022670 * 2 ^ 59
def prefixEnd_2022670 : Nat := 4983230072969 + 3 ^ 40 * 2022670 * 2
def baseEnd_2022670 : Nat := 461600851302091790232407

theorem tailTrace_2022670 : CollatzResearch.WordTrace tailWord_2022670 prefixEnd_2022670 461600851302091790232407 := by
  unfold tailWord_2022670
  simp only [CollatzResearch.WordTrace]
  refine ⟨9221604447777438672358183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49181890388146339585910309 9221604447777438672358183)
  ·
    refine ⟨13832406671666158008537275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9221604447777438672358183 13832406671666158008537275)
    ·
      refine ⟨20748610007499237012805913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13832406671666158008537275 20748610007499237012805913)
      ·
        refine ⟨15561457505624427759604435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20748610007499237012805913 15561457505624427759604435)
        ·
          refine ⟨23342186258436641639406653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15561457505624427759604435 23342186258436641639406653)
          ·
            refine ⟨8753319846913740614777495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23342186258436641639406653 8753319846913740614777495)
            ·
              refine ⟨13129979770370610922166243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8753319846913740614777495 13129979770370610922166243)
              ·
                refine ⟨19694969655555916383249365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13129979770370610922166243 19694969655555916383249365)
                ·
                  refine ⟨461600851302091790232407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19694969655555916383249365 461600851302091790232407)
                  ·
                    rfl

theorem cell21_2022670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 1, 7].length) (baseStart_2022670 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2022670 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2022670 prefixEnd_2022670 := by exact prefixLift 2022670
  have htrace : WordTrace (prefixWord ++ tailWord_2022670) baseStart_2022670 baseEnd_2022670 := by
    simpa [prefixWord, tailWord_2022670, baseEnd_2022670] using wordTrace_append hprefix tailTrace_2022670
  have hstable : (prefixWord ++ tailWord_2022670).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2022670).length < 2 ^ (prefixWord ++ tailWord_2022670).sum := by decide
  have hdescent : baseEnd_2022670 < baseStart_2022670 := by decide
  rcases family_descends (prefixWord ++ tailWord_2022670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2022732 : List Nat := [2, 2, 1, 3, 2, 2, 4, 5]
def baseStart_2022732 : Nat := 118140960795 + 2022732 * 2 ^ 59
def prefixEnd_2022732 : Nat := 4983230072969 + 3 ^ 40 * 2022732 * 2
def baseEnd_2022732 : Nat := 153871666848931153399649

theorem tailTrace_2022732 : CollatzResearch.WordTrace tailWord_2022732 prefixEnd_2022732 153871666848931153399649 := by
  unfold tailWord_2022732
  simp only [CollatzResearch.WordTrace]
  refine ⟨36887548453997446983811225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49183397938663262645081633 36887548453997446983811225)
  ·
    refine ⟨27665661340498085237858419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36887548453997446983811225 27665661340498085237858419)
    ·
      refine ⟨41498492010747127856787629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27665661340498085237858419 41498492010747127856787629)
      ·
        refine ⟨15561934504030172946295361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41498492010747127856787629 15561934504030172946295361)
        ·
          refine ⟨11671450878022629709721521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15561934504030172946295361 11671450878022629709721521)
          ·
            refine ⟨8753588158516972282291141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11671450878022629709721521 8753588158516972282291141)
            ·
              refine ⟨1641297779721932302929589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8753588158516972282291141 1641297779721932302929589)
              ·
                refine ⟨153871666848931153399649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1641297779721932302929589 153871666848931153399649)
                ·
                  rfl

theorem cell21_2022732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 4, 5].length) (baseStart_2022732 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2022732 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2022732 prefixEnd_2022732 := by exact prefixLift 2022732
  have htrace : WordTrace (prefixWord ++ tailWord_2022732) baseStart_2022732 baseEnd_2022732 := by
    simpa [prefixWord, tailWord_2022732, baseEnd_2022732] using wordTrace_append hprefix tailTrace_2022732
  have hstable : (prefixWord ++ tailWord_2022732).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2022732).length < 2 ^ (prefixWord ++ tailWord_2022732).sum := by decide
  have hdescent : baseEnd_2022732 < baseStart_2022732 := by decide
  rcases family_descends (prefixWord ++ tailWord_2022732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2022791 : List Nat := [1, 1, 4, 2, 2, 2, 2, 7]
def baseStart_2022791 : Nat := 118140960795 + 2022791 * 2 ^ 59
def prefixEnd_2022791 : Nat := 4983230072969 + 3 ^ 40 * 2022791 * 2
def baseEnd_2022791 : Nat := 153876155050207489571831

theorem tailTrace_2022791 : CollatzResearch.WordTrace tailWord_2022791 prefixEnd_2022791 153876155050207489571831 := by
  unfold tailWord_2022791
  simp only [CollatzResearch.WordTrace]
  refine ⟨73777248814781147044020227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49184832543187431362680151 73777248814781147044020227)
  ·
    refine ⟨110665873222171720566030341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73777248814781147044020227 110665873222171720566030341)
    ·
      refine ⟨20749851229157197606130689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 110665873222171720566030341 20749851229157197606130689)
      ·
        refine ⟨15562388421867898204598017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20749851229157197606130689 15562388421867898204598017)
        ·
          refine ⟨11671791316400923653448513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15562388421867898204598017 11671791316400923653448513)
          ·
            refine ⟨8753843487300692740086385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11671791316400923653448513 8753843487300692740086385)
            ·
              refine ⟨6565382615475519555064789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8753843487300692740086385 6565382615475519555064789)
              ·
                refine ⟨153876155050207489571831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6565382615475519555064789 153876155050207489571831)
                ·
                  rfl

theorem cell21_2022791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 2, 7].length) (baseStart_2022791 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2022791 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2022791 prefixEnd_2022791 := by exact prefixLift 2022791
  have htrace : WordTrace (prefixWord ++ tailWord_2022791) baseStart_2022791 baseEnd_2022791 := by
    simpa [prefixWord, tailWord_2022791, baseEnd_2022791] using wordTrace_append hprefix tailTrace_2022791
  have hstable : (prefixWord ++ tailWord_2022791).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2022791).length < 2 ^ (prefixWord ++ tailWord_2022791).sum := by decide
  have hdescent : baseEnd_2022791 < baseStart_2022791 := by decide
  rcases family_descends (prefixWord ++ tailWord_2022791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2022808 : List Nat := [2, 1, 2, 5, 3, 8]
def baseStart_2022808 : Nat := 118140960795 + 2022808 * 2 ^ 59
def prefixEnd_2022808 : Nat := 4983230072969 + 3 ^ 40 * 2022808 * 2
def baseEnd_2022808 : Nat := 17097494251193859886375

theorem tailTrace_2022808 : CollatzResearch.WordTrace tailWord_2022808 prefixEnd_2022808 17097494251193859886375 := by
  unfold tailWord_2022808
  simp only [CollatzResearch.WordTrace]
  refine ⟨36888934427859779473694539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49185245903813039298259385 36888934427859779473694539)
  ·
    refine ⟨55333401641789669210541809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36888934427859779473694539 55333401641789669210541809)
    ·
      refine ⟨41500051231342251907906357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55333401641789669210541809 41500051231342251907906357)
      ·
        refine ⟨3890629802938336116366221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 41500051231342251907906357 3890629802938336116366221)
        ·
          refine ⟨1458986176101876043637333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3890629802938336116366221 1458986176101876043637333)
          ·
            refine ⟨17097494251193859886375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1458986176101876043637333 17097494251193859886375)
            ·
              rfl

theorem cell21_2022808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 8].length) (baseStart_2022808 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2022808 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2022808 prefixEnd_2022808 := by exact prefixLift 2022808
  have htrace : WordTrace (prefixWord ++ tailWord_2022808) baseStart_2022808 baseEnd_2022808 := by
    simpa [prefixWord, tailWord_2022808, baseEnd_2022808] using wordTrace_append hprefix tailTrace_2022808
  have hstable : (prefixWord ++ tailWord_2022808).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2022808).length < 2 ^ (prefixWord ++ tailWord_2022808).sum := by decide
  have hdescent : baseEnd_2022808 < baseStart_2022808 := by decide
  rcases family_descends (prefixWord ++ tailWord_2022808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2022870 : List Nat := [5, 2, 1, 1, 1, 3, 1, 1, 6]
def baseStart_2022870 : Nat := 118140960795 + 2022870 * 2 ^ 59
def prefixEnd_2022870 : Nat := 4983230072969 + 3 ^ 40 * 2022870 * 2
def baseEnd_2022870 : Nat := 461646494026935886898665

theorem tailTrace_2022870 : CollatzResearch.WordTrace tailWord_2022870 prefixEnd_2022870 461646494026935886898665 := by
  unfold tailWord_2022870
  simp only [CollatzResearch.WordTrace]
  refine ⟨4611258136343433971009129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 49186753454329962357430709 4611258136343433971009129)
  ·
    refine ⟨3458443602257575478256847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4611258136343433971009129 3458443602257575478256847)
    ·
      refine ⟨5187665403386363217385271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3458443602257575478256847 5187665403386363217385271)
      ·
        refine ⟨7781498105079544826077907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5187665403386363217385271 7781498105079544826077907)
        ·
          refine ⟨11672247157619317239116861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7781498105079544826077907 11672247157619317239116861)
          ·
            refine ⟨4377092684107243964668823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11672247157619317239116861 4377092684107243964668823)
            ·
              refine ⟨6565639026160865947003235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4377092684107243964668823 6565639026160865947003235)
              ·
                refine ⟨9848458539241298920504853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6565639026160865947003235 9848458539241298920504853)
                ·
                  refine ⟨461646494026935886898665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9848458539241298920504853 461646494026935886898665)
                  ·
                    rfl

theorem cell21_2022870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 1, 1, 6].length) (baseStart_2022870 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2022870 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2022870 prefixEnd_2022870 := by exact prefixLift 2022870
  have htrace : WordTrace (prefixWord ++ tailWord_2022870) baseStart_2022870 baseEnd_2022870 := by
    simpa [prefixWord, tailWord_2022870, baseEnd_2022870] using wordTrace_append hprefix tailTrace_2022870
  have hstable : (prefixWord ++ tailWord_2022870).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2022870).length < 2 ^ (prefixWord ++ tailWord_2022870).sum := by decide
  have hdescent : baseEnd_2022870 < baseStart_2022870 := by decide
  rcases family_descends (prefixWord ++ tailWord_2022870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2022901 : List Nat := [1, 3, 5, 1, 1, 1, 4, 5]
def baseStart_2022901 : Nat := 118140960795 + 2022901 * 2 ^ 59
def prefixEnd_2022901 : Nat := 4983230072969 + 3 ^ 40 * 2022901 * 2
def baseEnd_2022901 : Nat := 153884522883095573960645

theorem tailTrace_2022901 : CollatzResearch.WordTrace tailWord_2022901 prefixEnd_2022901 153884522883095573960645 := by
  unfold tailWord_2022901
  simp only [CollatzResearch.WordTrace]
  refine ⟨73781260844382635830524557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49187507229588423887016371 73781260844382635830524557)
  ·
    refine ⟨27667972816643488436446709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73781260844382635830524557 27667972816643488436446709)
    ·
      refine ⟨2593872451560327040916879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 27667972816643488436446709 2593872451560327040916879)
      ·
        refine ⟨3890808677340490561375319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2593872451560327040916879 3890808677340490561375319)
        ·
          refine ⟨5836213016010735842062979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3890808677340490561375319 5836213016010735842062979)
          ·
            refine ⟨8754319524016103763094469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5836213016010735842062979 8754319524016103763094469)
            ·
              refine ⟨1641434910753019455580213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8754319524016103763094469 1641434910753019455580213)
              ·
                refine ⟨153884522883095573960645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1641434910753019455580213 153884522883095573960645)
                ·
                  rfl

theorem cell21_2022901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 4, 5].length) (baseStart_2022901 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2022901 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2022901 prefixEnd_2022901 := by exact prefixLift 2022901
  have htrace : WordTrace (prefixWord ++ tailWord_2022901) baseStart_2022901 baseEnd_2022901 := by
    simpa [prefixWord, tailWord_2022901, baseEnd_2022901] using wordTrace_append hprefix tailTrace_2022901
  have hstable : (prefixWord ++ tailWord_2022901).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2022901).length < 2 ^ (prefixWord ++ tailWord_2022901).sum := by decide
  have hdescent : baseEnd_2022901 < baseStart_2022901 := by decide
  rcases family_descends (prefixWord ++ tailWord_2022901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2022946 : List Nat := [3, 3, 1, 1, 1, 1, 6, 1, 4]
def baseStart_2022946 : Nat := 118140960795 + 2022946 * 2 ^ 59
def prefixEnd_2022946 : Nat := 4983230072969 + 3 ^ 40 * 2022946 * 2
def baseEnd_2022946 : Nat := 461663838262376643631843

theorem tailTrace_2022946 : CollatzResearch.WordTrace tailWord_2022946 prefixEnd_2022946 461663838262376643631843 := by
  unfold tailWord_2022946
  simp only [CollatzResearch.WordTrace]
  refine ⟨18445725532304902128978173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49188601419479739010608461 18445725532304902128978173)
  ·
    refine ⟨6917147074614338298366815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18445725532304902128978173 6917147074614338298366815)
    ·
      refine ⟨10375720611921507447550223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6917147074614338298366815 10375720611921507447550223)
      ·
        refine ⟨15563580917882261171325335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10375720611921507447550223 15563580917882261171325335)
        ·
          refine ⟨23345371376823391756988003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15563580917882261171325335 23345371376823391756988003)
          ·
            refine ⟨35018057065235087635482005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23345371376823391756988003 35018057065235087635482005)
            ·
              refine ⟨1641471424932894732913219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 35018057065235087635482005 1641471424932894732913219)
              ·
                refine ⟨2462207137399342099369829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1641471424932894732913219 2462207137399342099369829)
                ·
                  refine ⟨461663838262376643631843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2462207137399342099369829 461663838262376643631843)
                  ·
                    rfl

theorem cell21_2022946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 6, 1, 4].length) (baseStart_2022946 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2022946 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2022946 prefixEnd_2022946 := by exact prefixLift 2022946
  have htrace : WordTrace (prefixWord ++ tailWord_2022946) baseStart_2022946 baseEnd_2022946 := by
    simpa [prefixWord, tailWord_2022946, baseEnd_2022946] using wordTrace_append hprefix tailTrace_2022946
  have hstable : (prefixWord ++ tailWord_2022946).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2022946).length < 2 ^ (prefixWord ++ tailWord_2022946).sum := by decide
  have hdescent : baseEnd_2022946 < baseStart_2022946 := by decide
  rcases family_descends (prefixWord ++ tailWord_2022946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2023033 : List Nat := [1, 2, 1, 3, 3, 1, 1, 2, 7]
def baseStart_2023033 : Nat := 118140960795 + 2023033 * 2 ^ 59
def prefixEnd_2023033 : Nat := 4983230072969 + 3 ^ 40 * 2023033 * 2
def baseEnd_2023033 : Nat := 461683692847683825681665

theorem tailTrace_2023033 : CollatzResearch.WordTrace tailWord_2023033 prefixEnd_2023033 461683692847683825681665 := by
  unfold tailWord_2023033
  simp only [CollatzResearch.WordTrace]
  refine ⟨73786075279904422374329753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49190716853269614916219835 73786075279904422374329753)
  ·
    refine ⟨55339556459928316780747315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73786075279904422374329753 55339556459928316780747315)
    ·
      refine ⟨83009334689892475171120973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55339556459928316780747315 83009334689892475171120973)
      ·
        refine ⟨31128500508709678189170365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83009334689892475171120973 31128500508709678189170365)
        ·
          refine ⟨11673187690766129320938887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31128500508709678189170365 11673187690766129320938887)
          ·
            refine ⟨17509781536149193981408331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11673187690766129320938887 17509781536149193981408331)
            ·
              refine ⟨26264672304223790972112497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17509781536149193981408331 26264672304223790972112497)
              ·
                refine ⟨19698504228167843229084373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26264672304223790972112497 19698504228167843229084373)
                ·
                  refine ⟨461683692847683825681665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19698504228167843229084373 461683692847683825681665)
                  ·
                    rfl

theorem cell21_2023033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 2, 7].length) (baseStart_2023033 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2023033 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2023033 prefixEnd_2023033 := by exact prefixLift 2023033
  have htrace : WordTrace (prefixWord ++ tailWord_2023033) baseStart_2023033 baseEnd_2023033 := by
    simpa [prefixWord, tailWord_2023033, baseEnd_2023033] using wordTrace_append hprefix tailTrace_2023033
  have hstable : (prefixWord ++ tailWord_2023033).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2023033).length < 2 ^ (prefixWord ++ tailWord_2023033).sum := by decide
  have hdescent : baseEnd_2023033 < baseStart_2023033 := by decide
  rcases family_descends (prefixWord ++ tailWord_2023033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2023050 : List Nat := [3, 1, 2, 3, 2, 1, 1, 3, 5]
def baseStart_2023050 : Nat := 118140960795 + 2023050 * 2 ^ 59
def prefixEnd_2023050 : Nat := 4983230072969 + 3 ^ 40 * 2023050 * 2
def baseEnd_2023050 : Nat := 461687572479295573898297

theorem tailTrace_2023050 : CollatzResearch.WordTrace tailWord_2023050 prefixEnd_2023050 461687572479295573898297 := by
  unfold tailWord_2023050
  simp only [CollatzResearch.WordTrace]
  refine ⟨18446673830210708569424651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49191130213895222851799069 18446673830210708569424651)
  ·
    refine ⟨27670010745316062854136977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18446673830210708569424651 27670010745316062854136977)
    ·
      refine ⟨20752508058987047140602733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27670010745316062854136977 20752508058987047140602733)
      ·
        refine ⟨7782190522120142677726025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20752508058987047140602733 7782190522120142677726025)
        ·
          refine ⟨5836642891590107008294519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7782190522120142677726025 5836642891590107008294519)
          ·
            refine ⟨8754964337385160512441779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5836642891590107008294519 8754964337385160512441779)
            ·
              refine ⟨13132446506077740768662669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8754964337385160512441779 13132446506077740768662669)
              ·
                refine ⟨4924667439779152788248501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13132446506077740768662669 4924667439779152788248501)
                ·
                  refine ⟨461687572479295573898297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4924667439779152788248501 461687572479295573898297)
                  ·
                    rfl

theorem cell21_2023050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 3, 5].length) (baseStart_2023050 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2023050 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2023050 prefixEnd_2023050 := by exact prefixLift 2023050
  have htrace : WordTrace (prefixWord ++ tailWord_2023050) baseStart_2023050 baseEnd_2023050 := by
    simpa [prefixWord, tailWord_2023050, baseEnd_2023050] using wordTrace_append hprefix tailTrace_2023050
  have hstable : (prefixWord ++ tailWord_2023050).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2023050).length < 2 ^ (prefixWord ++ tailWord_2023050).sum := by decide
  have hdescent : baseEnd_2023050 < baseStart_2023050 := by decide
  rcases family_descends (prefixWord ++ tailWord_2023050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2023095 : List Nat := [1, 1, 3, 1, 5, 3, 7]
def baseStart_2023095 : Nat := 118140960795 + 2023095 * 2 ^ 59
def prefixEnd_2023095 : Nat := 4983230072969 + 3 ^ 40 * 2023095 * 2
def baseEnd_2023095 : Nat := 51299760232487277294245

theorem tailTrace_2023095 : CollatzResearch.WordTrace tailWord_2023095 prefixEnd_2023095 51299760232487277294245 := by
  unfold tailWord_2023095
  simp only [CollatzResearch.WordTrace]
  refine ⟨73788336605679806963086739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49192224403786537975391159 73788336605679806963086739)
  ·
    refine ⟨110682504908519710444630109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73788336605679806963086739 110682504908519710444630109)
    ·
      refine ⟨41505939340694891416736291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110682504908519710444630109 41505939340694891416736291)
      ·
        refine ⟨62258909011042337125104437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41505939340694891416736291 62258909011042337125104437)
        ·
          refine ⟨5836772719785219105478541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 62258909011042337125104437 5836772719785219105478541)
          ·
            refine ⟨2188789769919457164554453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5836772719785219105478541 2188789769919457164554453)
            ·
              refine ⟨51299760232487277294245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2188789769919457164554453 51299760232487277294245)
              ·
                rfl

theorem cell21_2023095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 7].length) (baseStart_2023095 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2023095 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2023095 prefixEnd_2023095 := by exact prefixLift 2023095
  have htrace : WordTrace (prefixWord ++ tailWord_2023095) baseStart_2023095 baseEnd_2023095 := by
    simpa [prefixWord, tailWord_2023095, baseEnd_2023095] using wordTrace_append hprefix tailTrace_2023095
  have hstable : (prefixWord ++ tailWord_2023095).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2023095).length < 2 ^ (prefixWord ++ tailWord_2023095).sum := by decide
  have hdescent : baseEnd_2023095 < baseStart_2023095 := by decide
  rcases family_descends (prefixWord ++ tailWord_2023095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2023329 : List Nat := [1, 2, 3, 4, 2, 2, 2, 2, 3]
def baseStart_2023329 : Nat := 118140960795 + 2023329 * 2 ^ 59
def prefixEnd_2023329 : Nat := 4983230072969 + 3 ^ 40 * 2023329 * 2
def baseEnd_2023329 : Nat := 461751244080453088747727

theorem tailTrace_2023329 : CollatzResearch.WordTrace tailWord_2023329 prefixEnd_2023329 461751244080453088747727 := by
  unfold tailWord_2023329
  simp only [CollatzResearch.WordTrace]
  refine ⟨73796871286832064927105041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49197914191221376618070027 73796871286832064927105041)
  ·
    refine ⟨55347653465124048695328781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73796871286832064927105041 55347653465124048695328781)
    ·
      refine ⟨20755370049421518260748293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55347653465124048695328781 20755370049421518260748293)
      ·
        refine ⟨3891631884266534673890305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20755370049421518260748293 3891631884266534673890305)
        ·
          refine ⟨2918723913199901005417729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3891631884266534673890305 2918723913199901005417729)
          ·
            refine ⟨2189042934899925754063297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2918723913199901005417729 2189042934899925754063297)
            ·
              refine ⟨1641782201174944315547473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2189042934899925754063297 1641782201174944315547473)
              ·
                refine ⟨1231336650881208236660605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1641782201174944315547473 1231336650881208236660605)
                ·
                  refine ⟨461751244080453088747727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1231336650881208236660605 461751244080453088747727)
                  ·
                    rfl

theorem cell21_2023329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 2, 2, 3].length) (baseStart_2023329 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2023329 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2023329 prefixEnd_2023329 := by exact prefixLift 2023329
  have htrace : WordTrace (prefixWord ++ tailWord_2023329) baseStart_2023329 baseEnd_2023329 := by
    simpa [prefixWord, tailWord_2023329, baseEnd_2023329] using wordTrace_append hprefix tailTrace_2023329
  have hstable : (prefixWord ++ tailWord_2023329).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2023329).length < 2 ^ (prefixWord ++ tailWord_2023329).sum := by decide
  have hdescent : baseEnd_2023329 < baseStart_2023329 := by decide
  rcases family_descends (prefixWord ++ tailWord_2023329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2023351 : List Nat := [1, 1, 3, 1, 3, 1, 1, 2, 8]
def baseStart_2023351 : Nat := 118140960795 + 2023351 * 2 ^ 59
def prefixEnd_2023351 : Nat := 4983230072969 + 3 ^ 40 * 2023351 * 2
def baseEnd_2023351 : Nat := 461756264780185939381015

theorem tailTrace_2023351 : CollatzResearch.WordTrace tailWord_2023351 prefixEnd_2023351 461756264780185939381015 := by
  unfold tailWord_2023351
  simp only [CollatzResearch.WordTrace]
  refine ⟨73797673692752362684405907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49198449128501575122937271 73797673692752362684405907)
  ·
    refine ⟨110696510539128544026608861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73797673692752362684405907 110696510539128544026608861)
    ·
      refine ⟨41511191452173204009978323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110696510539128544026608861 41511191452173204009978323)
      ·
        refine ⟨62266787178259806014967485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41511191452173204009978323 62266787178259806014967485)
        ·
          refine ⟨23350045191847427255612807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62266787178259806014967485 23350045191847427255612807)
          ·
            refine ⟨35025067787771140883419211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23350045191847427255612807 35025067787771140883419211)
            ·
              refine ⟨52537601681656711325128817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35025067787771140883419211 52537601681656711325128817)
              ·
                refine ⟨39403201261242533493846613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52537601681656711325128817 39403201261242533493846613)
                ·
                  refine ⟨461756264780185939381015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39403201261242533493846613 461756264780185939381015)
                  ·
                    rfl

theorem cell21_2023351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 2, 8].length) (baseStart_2023351 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2023351 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2023351 prefixEnd_2023351 := by exact prefixLift 2023351
  have htrace : WordTrace (prefixWord ++ tailWord_2023351) baseStart_2023351 baseEnd_2023351 := by
    simpa [prefixWord, tailWord_2023351, baseEnd_2023351] using wordTrace_append hprefix tailTrace_2023351
  have hstable : (prefixWord ++ tailWord_2023351).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2023351).length < 2 ^ (prefixWord ++ tailWord_2023351).sum := by decide
  have hdescent : baseEnd_2023351 < baseStart_2023351 := by decide
  rcases family_descends (prefixWord ++ tailWord_2023351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2023447 : List Nat := [1, 1, 3, 5, 2, 2, 1, 1, 5]
def baseStart_2023447 : Nat := 118140960795 + 2023447 * 2 ^ 59
def prefixEnd_2023447 : Nat := 4983230072969 + 3 ^ 40 * 2023447 * 2
def baseEnd_2023447 : Nat := 461778173288111105780819

theorem tailTrace_2023447 : CollatzResearch.WordTrace tailWord_2023447 prefixEnd_2023447 461778173288111105780819 := by
  unfold tailWord_2023447
  simp only [CollatzResearch.WordTrace]
  refine ⟨73801175100404571079900595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49200783400269714053267063 73801175100404571079900595)
  ·
    refine ⟨110701762650606856619850893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73801175100404571079900595 110701762650606856619850893)
    ·
      refine ⟨41513160993977571232444085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110701762650606856619850893 41513160993977571232444085)
      ·
        refine ⟨3891858843185397303041633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 41513160993977571232444085 3891858843185397303041633)
        ·
          refine ⟨2918894132389047977281225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3891858843185397303041633 2918894132389047977281225)
          ·
            refine ⟨2189170599291785982960919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2918894132389047977281225 2189170599291785982960919)
            ·
              refine ⟨3283755898937678974441379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2189170599291785982960919 3283755898937678974441379)
              ·
                refine ⟨4925633848406518461662069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3283755898937678974441379 4925633848406518461662069)
                ·
                  refine ⟨461778173288111105780819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4925633848406518461662069 461778173288111105780819)
                  ·
                    rfl

theorem cell21_2023447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 1, 1, 5].length) (baseStart_2023447 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2023447 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2023447 prefixEnd_2023447 := by exact prefixLift 2023447
  have htrace : WordTrace (prefixWord ++ tailWord_2023447) baseStart_2023447 baseEnd_2023447 := by
    simpa [prefixWord, tailWord_2023447, baseEnd_2023447] using wordTrace_append hprefix tailTrace_2023447
  have hstable : (prefixWord ++ tailWord_2023447).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2023447).length < 2 ^ (prefixWord ++ tailWord_2023447).sum := by decide
  have hdescent : baseEnd_2023447 < baseStart_2023447 := by decide
  rcases family_descends (prefixWord ++ tailWord_2023447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2023461 : List Nat := [1, 3, 1, 2, 2, 3, 4, 1, 4]
def baseStart_2023461 : Nat := 118140960795 + 2023461 * 2 ^ 59
def prefixEnd_2023461 : Nat := 4983230072969 + 3 ^ 40 * 2023461 * 2
def baseEnd_2023461 : Nat := 461781368278850192547457

theorem tailTrace_2023461 : CollatzResearch.WordTrace tailWord_2023461 prefixEnd_2023461 461781368278850192547457 := by
  unfold tailWord_2023461
  simp only [CollatzResearch.WordTrace]
  refine ⟨73801685722353851470910237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49201123814902567647273491 73801685722353851470910237)
  ·
    refine ⟨27675632145882694301591339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73801685722353851470910237 27675632145882694301591339)
    ·
      refine ⟨41513448218824041452387009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27675632145882694301591339 41513448218824041452387009)
      ·
        refine ⟨31135086164118031089290257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41513448218824041452387009 31135086164118031089290257)
        ·
          refine ⟨23351314623088523316967693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31135086164118031089290257 23351314623088523316967693)
          ·
            refine ⟨8756742983658196243862885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23351314623088523316967693 8756742983658196243862885)
            ·
              refine ⟨1641889309435911795724291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8756742983658196243862885 1641889309435911795724291)
              ·
                refine ⟨2462833964153867693586437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1641889309435911795724291 2462833964153867693586437)
                ·
                  refine ⟨461781368278850192547457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2462833964153867693586437 461781368278850192547457)
                  ·
                    rfl

theorem cell21_2023461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 4, 1, 4].length) (baseStart_2023461 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2023461 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2023461 prefixEnd_2023461 := by exact prefixLift 2023461
  have htrace : WordTrace (prefixWord ++ tailWord_2023461) baseStart_2023461 baseEnd_2023461 := by
    simpa [prefixWord, tailWord_2023461, baseEnd_2023461] using wordTrace_append hprefix tailTrace_2023461
  have hstable : (prefixWord ++ tailWord_2023461).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2023461).length < 2 ^ (prefixWord ++ tailWord_2023461).sum := by decide
  have hdescent : baseEnd_2023461 < baseStart_2023461 := by decide
  rcases family_descends (prefixWord ++ tailWord_2023461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2023520 : List Nat := [2, 1, 1, 3, 2, 3, 2, 3, 4]
def baseStart_2023520 : Nat := 118140960795 + 2023520 * 2 ^ 59
def prefixEnd_2023520 : Nat := 4983230072969 + 3 ^ 40 * 2023520 * 2
def baseEnd_2023520 : Nat := 461794832882679201064003

theorem tailTrace_2023520 : CollatzResearch.WordTrace tailWord_2023520 prefixEnd_2023520 461794832882679201064003 := by
  unfold tailWord_2023520
  simp only [CollatzResearch.WordTrace]
  refine ⟨36901918814570052273654007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49202558419426736364872009 36901918814570052273654007)
  ·
    refine ⟨55352878221855078410481011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36901918814570052273654007 55352878221855078410481011)
    ·
      refine ⟨83029317332782617615721517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55352878221855078410481011 83029317332782617615721517)
      ·
        refine ⟨31135993999793481605895569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83029317332782617615721517 31135993999793481605895569)
        ·
          refine ⟨23351995499845111204421677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31135993999793481605895569 23351995499845111204421677)
          ·
            refine ⟨8756998312441916701658129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23351995499845111204421677 8756998312441916701658129)
            ·
              refine ⟨6567748734331437526243597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8756998312441916701658129 6567748734331437526243597)
              ·
                refine ⟨2462905775374289072341349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6567748734331437526243597 2462905775374289072341349)
                ·
                  refine ⟨461794832882679201064003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2462905775374289072341349 461794832882679201064003)
                  ·
                    rfl

theorem cell21_2023520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 2, 3, 4].length) (baseStart_2023520 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2023520 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2023520 prefixEnd_2023520 := by exact prefixLift 2023520
  have htrace : WordTrace (prefixWord ++ tailWord_2023520) baseStart_2023520 baseEnd_2023520 := by
    simpa [prefixWord, tailWord_2023520, baseEnd_2023520] using wordTrace_append hprefix tailTrace_2023520
  have hstable : (prefixWord ++ tailWord_2023520).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2023520).length < 2 ^ (prefixWord ++ tailWord_2023520).sum := by decide
  have hdescent : baseEnd_2023520 < baseStart_2023520 := by decide
  rcases family_descends (prefixWord ++ tailWord_2023520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2023630 : List Nat := [4, 1, 1, 1, 4, 3, 2, 1, 4]
def baseStart_2023630 : Nat := 118140960795 + 2023630 * 2 ^ 59
def prefixEnd_2023630 : Nat := 4983230072969 + 3 ^ 40 * 2023630 * 2
def baseEnd_2023630 : Nat := 461819936381343454230445

theorem tailTrace_2023630 : CollatzResearch.WordTrace tailWord_2023630 prefixEnd_2023630 461819936381343454230445 := by
  unfold tailWord_2023630
  simp only [CollatzResearch.WordTrace]
  refine ⟨9225981207342699166726543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49205233105827728889208229 9225981207342699166726543)
  ·
    refine ⟨13838971811014048750089815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9225981207342699166726543 13838971811014048750089815)
    ·
      refine ⟨20758457716521073125134723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13838971811014048750089815 20758457716521073125134723)
      ·
        refine ⟨31137686574781609687702085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20758457716521073125134723 31137686574781609687702085)
        ·
          refine ⟨5838316232771551816444141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31137686574781609687702085 5838316232771551816444141)
          ·
            refine ⟨2189368587289331931166553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5838316232771551816444141 2189368587289331931166553)
            ·
              refine ⟨1642026440466998948374915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2189368587289331931166553 1642026440466998948374915)
              ·
                refine ⟨2463039660700498422562373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1642026440466998948374915 2463039660700498422562373)
                ·
                  refine ⟨461819936381343454230445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2463039660700498422562373 461819936381343454230445)
                  ·
                    rfl

theorem cell21_2023630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 2, 1, 4].length) (baseStart_2023630 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2023630 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2023630 prefixEnd_2023630 := by exact prefixLift 2023630
  have htrace : WordTrace (prefixWord ++ tailWord_2023630) baseStart_2023630 baseEnd_2023630 := by
    simpa [prefixWord, tailWord_2023630, baseEnd_2023630] using wordTrace_append hprefix tailTrace_2023630
  have hstable : (prefixWord ++ tailWord_2023630).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2023630).length < 2 ^ (prefixWord ++ tailWord_2023630).sum := by decide
  have hdescent : baseEnd_2023630 < baseStart_2023630 := by decide
  rcases family_descends (prefixWord ++ tailWord_2023630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2023658 : List Nat := [3, 1, 3, 1, 1, 2, 2, 5, 3]
def baseStart_2023658 : Nat := 118140960795 + 2023658 * 2 ^ 59
def prefixEnd_2023658 : Nat := 4983230072969 + 3 ^ 40 * 2023658 * 2
def baseEnd_2023658 : Nat := 461826326362821627763721

theorem tailTrace_2023658 : CollatzResearch.WordTrace tailWord_2023658 prefixEnd_2023658 461826326362821627763721 := by
  unfold tailWord_2023658
  simp only [CollatzResearch.WordTrace]
  refine ⟨18452217725660038528957907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49205913935093436077221085 18452217725660038528957907)
  ·
    refine ⟨27678326588490057793436861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18452217725660038528957907 27678326588490057793436861)
    ·
      refine ⟨10379372470683771672538823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27678326588490057793436861 10379372470683771672538823)
      ·
        refine ⟨15569058706025657508808235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10379372470683771672538823 15569058706025657508808235)
        ·
          refine ⟨23353588059038486263212353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15569058706025657508808235 23353588059038486263212353)
          ·
            refine ⟨17515191044278864697409265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23353588059038486263212353 17515191044278864697409265)
            ·
              refine ⟨13136393283209148523056949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17515191044278864697409265 13136393283209148523056949)
              ·
                refine ⟨1231536870300857674036589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13136393283209148523056949 1231536870300857674036589)
                ·
                  refine ⟨461826326362821627763721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1231536870300857674036589 461826326362821627763721)
                  ·
                    rfl

theorem cell21_2023658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 5, 3].length) (baseStart_2023658 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2023658 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2023658 prefixEnd_2023658 := by exact prefixLift 2023658
  have htrace : WordTrace (prefixWord ++ tailWord_2023658) baseStart_2023658 baseEnd_2023658 := by
    simpa [prefixWord, tailWord_2023658, baseEnd_2023658] using wordTrace_append hprefix tailTrace_2023658
  have hstable : (prefixWord ++ tailWord_2023658).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2023658).length < 2 ^ (prefixWord ++ tailWord_2023658).sum := by decide
  have hdescent : baseEnd_2023658 < baseStart_2023658 := by decide
  rcases family_descends (prefixWord ++ tailWord_2023658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2023669 : List Nat := [1, 3, 17]
def baseStart_2023669 : Nat := 118140960795 + 2023669 * 2 ^ 59
def prefixEnd_2023669 : Nat := 4983230072969 + 3 ^ 40 * 2023669 * 2
def baseEnd_2023669 : Nat := 633510064077761389685

theorem tailTrace_2023669 : CollatzResearch.WordTrace tailWord_2023669 prefixEnd_2023669 633510064077761389685 := by
  unfold tailWord_2023669
  simp only [CollatzResearch.WordTrace]
  refine ⟨73809272105600302994482061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49206181403733535329654707 73809272105600302994482061)
  ·
    refine ⟨27678477039600113622930773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73809272105600302994482061 27678477039600113622930773)
    ·
      refine ⟨633510064077761389685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 17 27678477039600113622930773 633510064077761389685)
      ·
        rfl

theorem cell21_2023669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 17].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 17].length) (baseStart_2023669 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2023669 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2023669 prefixEnd_2023669 := by exact prefixLift 2023669
  have htrace : WordTrace (prefixWord ++ tailWord_2023669) baseStart_2023669 baseEnd_2023669 := by
    simpa [prefixWord, tailWord_2023669, baseEnd_2023669] using wordTrace_append hprefix tailTrace_2023669
  have hstable : (prefixWord ++ tailWord_2023669).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2023669).length < 2 ^ (prefixWord ++ tailWord_2023669).sum := by decide
  have hdescent : baseEnd_2023669 < baseStart_2023669 := by decide
  rcases family_descends (prefixWord ++ tailWord_2023669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2023703 : List Nat := [1, 1, 3, 4, 1, 3, 3, 5]
def baseStart_2023703 : Nat := 118140960795 + 2023703 * 2 ^ 59
def prefixEnd_2023703 : Nat := 4983230072969 + 3 ^ 40 * 2023703 * 2
def baseEnd_2023703 : Nat := 153945531991970516504543

theorem tailTrace_2023703 : CollatzResearch.WordTrace tailWord_2023703 prefixEnd_2023703 153945531991970516504543 := by
  unfold tailWord_2023703
  simp only [CollatzResearch.WordTrace]
  refine ⟨73810512187477126801219763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49207008124984751200813175 73810512187477126801219763)
  ·
    refine ⟨110715768281215690201829645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73810512187477126801219763 110715768281215690201829645)
    ·
      refine ⟨41518413105455883825686117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110715768281215690201829645 41518413105455883825686117)
      ·
        refine ⟨7784702457272978217316147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41518413105455883825686117 7784702457272978217316147)
        ·
          refine ⟨11677053685909467325974221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7784702457272978217316147 11677053685909467325974221)
          ·
            refine ⟨4378895132216050247240333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11677053685909467325974221 4378895132216050247240333)
            ·
              refine ⟨1642085674581018842715125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4378895132216050247240333 1642085674581018842715125)
              ·
                refine ⟨153945531991970516504543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1642085674581018842715125 153945531991970516504543)
                ·
                  rfl

theorem cell21_2023703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 3, 5].length) (baseStart_2023703 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2023703 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2023703 prefixEnd_2023703 := by exact prefixLift 2023703
  have htrace : WordTrace (prefixWord ++ tailWord_2023703) baseStart_2023703 baseEnd_2023703 := by
    simpa [prefixWord, tailWord_2023703, baseEnd_2023703] using wordTrace_append hprefix tailTrace_2023703
  have hstable : (prefixWord ++ tailWord_2023703).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2023703).length < 2 ^ (prefixWord ++ tailWord_2023703).sum := by decide
  have hdescent : baseEnd_2023703 < baseStart_2023703 := by decide
  rcases family_descends (prefixWord ++ tailWord_2023703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2023731 : List Nat := [1, 1, 1, 2, 5, 1, 3, 1, 6]
def baseStart_2023731 : Nat := 118140960795 + 2023731 * 2 ^ 59
def prefixEnd_2023731 : Nat := 4983230072969 + 3 ^ 40 * 2023731 * 2
def baseEnd_2023731 : Nat := 461842985957389723046905

theorem tailTrace_2023731 : CollatzResearch.WordTrace tailWord_2023731 prefixEnd_2023731 461842985957389723046905 := by
  unfold tailWord_2023731
  simp only [CollatzResearch.WordTrace]
  refine ⟨73811533431375687583239047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49207688954250458388826031 73811533431375687583239047)
  ·
    refine ⟨110717300147063531374858571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73811533431375687583239047 110717300147063531374858571)
    ·
      refine ⟨166075950220595297062287857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110717300147063531374858571 166075950220595297062287857)
      ·
        refine ⟨124556962665446472796715893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166075950220595297062287857 124556962665446472796715893)
        ·
          refine ⟨11677215249885606824692115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 124556962665446472796715893 11677215249885606824692115)
          ·
            refine ⟨17515822874828410237038173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11677215249885606824692115 17515822874828410237038173)
            ·
              refine ⟨6568433578060653838889315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17515822874828410237038173 6568433578060653838889315)
              ·
                refine ⟨9852650367090980758333973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6568433578060653838889315 9852650367090980758333973)
                ·
                  refine ⟨461842985957389723046905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9852650367090980758333973 461842985957389723046905)
                  ·
                    rfl

theorem cell21_2023731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 3, 1, 6].length) (baseStart_2023731 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2023731 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2023731 prefixEnd_2023731 := by exact prefixLift 2023731
  have htrace : WordTrace (prefixWord ++ tailWord_2023731) baseStart_2023731 baseEnd_2023731 := by
    simpa [prefixWord, tailWord_2023731, baseEnd_2023731] using wordTrace_append hprefix tailTrace_2023731
  have hstable : (prefixWord ++ tailWord_2023731).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2023731).length < 2 ^ (prefixWord ++ tailWord_2023731).sum := by decide
  have hdescent : baseEnd_2023731 < baseStart_2023731 := by decide
  rcases family_descends (prefixWord ++ tailWord_2023731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2023807 : List Nat := [1, 1, 2, 2, 1, 1, 2, 7, 4]
def baseStart_2023807 : Nat := 118140960795 + 2023807 * 2 ^ 59
def prefixEnd_2023807 : Nat := 4983230072969 + 3 ^ 40 * 2023807 * 2
def baseEnd_2023807 : Nat := 461860330192830479780083

theorem tailTrace_2023807 : CollatzResearch.WordTrace tailWord_2023807 prefixEnd_2023807 461860330192830479780083 := by
  unfold tailWord_2023807
  simp only [CollatzResearch.WordTrace]
  refine ⟨73814305379100352563005675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49209536919400235042003783 73814305379100352563005675)
  ·
    refine ⟨110721458068650528844508513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73814305379100352563005675 110721458068650528844508513)
    ·
      refine ⟨83041093551487896633381385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110721458068650528844508513 83041093551487896633381385)
      ·
        refine ⟨62280820163615922475036039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83041093551487896633381385 62280820163615922475036039)
        ·
          refine ⟨93421230245423883712554059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62280820163615922475036039 93421230245423883712554059)
          ·
            refine ⟨140131845368135825568831089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93421230245423883712554059 140131845368135825568831089)
            ·
              refine ⟨105098884026101869176623317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140131845368135825568831089 105098884026101869176623317)
              ·
                refine ⟨2463255094361762558827109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 105098884026101869176623317 2463255094361762558827109)
                ·
                  refine ⟨461860330192830479780083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2463255094361762558827109 461860330192830479780083)
                  ·
                    rfl

theorem cell21_2023807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 7, 4].length) (baseStart_2023807 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2023807 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2023807 prefixEnd_2023807 := by exact prefixLift 2023807
  have htrace : WordTrace (prefixWord ++ tailWord_2023807) baseStart_2023807 baseEnd_2023807 := by
    simpa [prefixWord, tailWord_2023807, baseEnd_2023807] using wordTrace_append hprefix tailTrace_2023807
  have hstable : (prefixWord ++ tailWord_2023807).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2023807).length < 2 ^ (prefixWord ++ tailWord_2023807).sum := by decide
  have hdescent : baseEnd_2023807 < baseStart_2023807 := by decide
  rcases family_descends (prefixWord ++ tailWord_2023807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2023852 : List Nat := [2, 2, 1, 1, 1, 1, 3, 5, 5]
def baseStart_2023852 : Nat := 118140960795 + 2023852 * 2 ^ 59
def prefixEnd_2023852 : Nat := 4983230072969 + 3 ^ 40 * 2023852 * 2
def baseEnd_2023852 : Nat := 461870599805920401529991

theorem tailTrace_2023852 : CollatzResearch.WordTrace tailWord_2023852 prefixEnd_2023852 461870599805920401529991 := by
  unfold tailWord_2023852
  simp only [CollatzResearch.WordTrace]
  refine ⟨36907973331968662624196905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49210631109291550165595873 36907973331968662624196905)
  ·
    refine ⟨27680979998976496968147679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36907973331968662624196905 27680979998976496968147679)
    ·
      refine ⟨41521469998464745452221519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27680979998976496968147679 41521469998464745452221519)
      ·
        refine ⟨62282204997697118178332279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41521469998464745452221519 62282204997697118178332279)
        ·
          refine ⟨93423307496545677267498419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62282204997697118178332279 93423307496545677267498419)
          ·
            refine ⟨140134961244818515901247629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93423307496545677267498419 140134961244818515901247629)
            ·
              refine ⟨52550610466806943462967861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 140134961244818515901247629 52550610466806943462967861)
              ·
                refine ⟨4926619731263150949653237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52550610466806943462967861 4926619731263150949653237)
                ·
                  refine ⟨461870599805920401529991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4926619731263150949653237 461870599805920401529991)
                  ·
                    rfl

theorem cell21_2023852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 5].length) (baseStart_2023852 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2023852 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2023852 prefixEnd_2023852 := by exact prefixLift 2023852
  have htrace : WordTrace (prefixWord ++ tailWord_2023852) baseStart_2023852 baseEnd_2023852 := by
    simpa [prefixWord, tailWord_2023852, baseEnd_2023852] using wordTrace_append hprefix tailTrace_2023852
  have hstable : (prefixWord ++ tailWord_2023852).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2023852).length < 2 ^ (prefixWord ++ tailWord_2023852).sum := by decide
  have hdescent : baseEnd_2023852 < baseStart_2023852 := by decide
  rcases family_descends (prefixWord ++ tailWord_2023852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2023869 : List Nat := [1, 4, 1, 2, 2, 3, 1, 2, 5]
def baseStart_2023869 : Nat := 118140960795 + 2023869 * 2 ^ 59
def prefixEnd_2023869 : Nat := 4983230072969 + 3 ^ 40 * 2023869 * 2
def baseEnd_2023869 : Nat := 461874479437532149746623

theorem tailTrace_2023869 : CollatzResearch.WordTrace tailWord_2023869 prefixEnd_2023869 461874479437532149746623 := by
  unfold tailWord_2023869
  simp only [CollatzResearch.WordTrace]
  refine ⟨73816566704875737151762661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49211044469917158101175107 73816566704875737151762661)
  ·
    refine ⟨13840606257164200715955499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73816566704875737151762661 13840606257164200715955499)
    ·
      refine ⟨20760909385746301073933249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13840606257164200715955499 20760909385746301073933249)
      ·
        refine ⟨15570682039309725805449937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20760909385746301073933249 15570682039309725805449937)
        ·
          refine ⟨11678011529482294354087453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15570682039309725805449937 11678011529482294354087453)
          ·
            refine ⟨4379254323555860382782795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11678011529482294354087453 4379254323555860382782795)
            ·
              refine ⟨6568881485333790574174193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4379254323555860382782795 6568881485333790574174193)
              ·
                refine ⟨4926661114000342930630645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6568881485333790574174193 4926661114000342930630645)
                ·
                  refine ⟨461874479437532149746623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4926661114000342930630645 461874479437532149746623)
                  ·
                    rfl

theorem cell21_2023869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 1, 2, 5].length) (baseStart_2023869 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2023869 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2023869 prefixEnd_2023869 := by exact prefixLift 2023869
  have htrace : WordTrace (prefixWord ++ tailWord_2023869) baseStart_2023869 baseEnd_2023869 := by
    simpa [prefixWord, tailWord_2023869, baseEnd_2023869] using wordTrace_append hprefix tailTrace_2023869
  have hstable : (prefixWord ++ tailWord_2023869).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2023869).length < 2 ^ (prefixWord ++ tailWord_2023869).sum := by decide
  have hdescent : baseEnd_2023869 < baseStart_2023869 := by decide
  rcases family_descends (prefixWord ++ tailWord_2023869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2023897 : List Nat := [1, 2, 1, 2, 4, 1, 10]
def baseStart_2023897 : Nat := 118140960795 + 2023897 * 2 ^ 59
def prefixEnd_2023897 : Nat := 4983230072969 + 3 ^ 40 * 2023897 * 2
def baseEnd_2023897 : Nat := 51320096602112258142211

theorem tailTrace_2023897 : CollatzResearch.WordTrace tailWord_2023897 prefixEnd_2023897 51320096602112258142211 := by
  unfold tailWord_2023897
  simp only [CollatzResearch.WordTrace]
  refine ⟨73817587948774297933781945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49211725299182865289187963 73817587948774297933781945)
  ·
    refine ⟨55363190961580723450336459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73817587948774297933781945 55363190961580723450336459)
    ·
      refine ⟨83044786442371085175504689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55363190961580723450336459 83044786442371085175504689)
      ·
        refine ⟨62283589831778313881628517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83044786442371085175504689 62283589831778313881628517)
        ·
          refine ⟨11678173093458433852805347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62283589831778313881628517 11678173093458433852805347)
          ·
            refine ⟨17517259640187650779208021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11678173093458433852805347 17517259640187650779208021)
            ·
              refine ⟨51320096602112258142211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 17517259640187650779208021 51320096602112258142211)
              ·
                rfl

theorem cell21_2023897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 10].length) (baseStart_2023897 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2023897 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2023897 prefixEnd_2023897 := by exact prefixLift 2023897
  have htrace : WordTrace (prefixWord ++ tailWord_2023897) baseStart_2023897 baseEnd_2023897 := by
    simpa [prefixWord, tailWord_2023897, baseEnd_2023897] using wordTrace_append hprefix tailTrace_2023897
  have hstable : (prefixWord ++ tailWord_2023897).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2023897).length < 2 ^ (prefixWord ++ tailWord_2023897).sum := by decide
  have hdescent : baseEnd_2023897 < baseStart_2023897 := by decide
  rcases family_descends (prefixWord ++ tailWord_2023897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2023928 : List Nat := [2, 1, 2, 1, 1, 4, 1, 4, 5]
def baseStart_2023928 : Nat := 118140960795 + 2023928 * 2 ^ 59
def prefixEnd_2023928 : Nat := 4983230072969 + 3 ^ 40 * 2023928 * 2
def baseEnd_2023928 : Nat := 461887944041361158263169

theorem tailTrace_2023928 : CollatzResearch.WordTrace tailWord_2023928 prefixEnd_2023928 461887944041361158263169 := by
  unfold tailWord_2023928
  simp only [CollatzResearch.WordTrace]
  refine ⟨36909359305830995114080219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49212479074441326818773625 36909359305830995114080219)
  ·
    refine ⟨55364038958746492671120329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36909359305830995114080219 55364038958746492671120329)
    ·
      refine ⟨41523029219059869503340247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55364038958746492671120329 41523029219059869503340247)
      ·
        refine ⟨62284543828589804255010371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41523029219059869503340247 62284543828589804255010371)
        ·
          refine ⟨93426815742884706382515557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62284543828589804255010371 93426815742884706382515557)
          ·
            refine ⟨17517527951790882446721667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 93426815742884706382515557 17517527951790882446721667)
            ·
              refine ⟨26276291927686323670082501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17517527951790882446721667 26276291927686323670082501)
              ·
                refine ⟨4926804736441185688140469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26276291927686323670082501 4926804736441185688140469)
                ·
                  refine ⟨461887944041361158263169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4926804736441185688140469 461887944041361158263169)
                  ·
                    rfl

theorem cell21_2023928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 4, 5].length) (baseStart_2023928 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2023928 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2023928 prefixEnd_2023928 := by exact prefixLift 2023928
  have htrace : WordTrace (prefixWord ++ tailWord_2023928) baseStart_2023928 baseEnd_2023928 := by
    simpa [prefixWord, tailWord_2023928, baseEnd_2023928] using wordTrace_append hprefix tailTrace_2023928
  have hstable : (prefixWord ++ tailWord_2023928).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2023928).length < 2 ^ (prefixWord ++ tailWord_2023928).sum := by decide
  have hdescent : baseEnd_2023928 < baseStart_2023928 := by decide
  rcases family_descends (prefixWord ++ tailWord_2023928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2023945 : List Nat := [1, 2, 1, 1, 3, 1, 2, 7, 3]
def baseStart_2023945 : Nat := 118140960795 + 2023945 * 2 ^ 59
def prefixEnd_2023945 : Nat := 4983230072969 + 3 ^ 40 * 2023945 * 2
def baseEnd_2023945 : Nat := 461891823672972906479801

theorem tailTrace_2023945 : CollatzResearch.WordTrace tailWord_2023945 prefixEnd_2023945 461891823672972906479801 := by
  unfold tailWord_2023945
  simp only [CollatzResearch.WordTrace]
  refine ⟨73819338652600402131529289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49212892435066934754352859 73819338652600402131529289)
  ·
    refine ⟨55364503989450301598646967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73819338652600402131529289 55364503989450301598646967)
    ·
      refine ⟨83046755984175452397970451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55364503989450301598646967 83046755984175452397970451)
      ·
        refine ⟨124570133976263178596955677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83046755984175452397970451 124570133976263178596955677)
        ·
          refine ⟨46713800241098691973858379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124570133976263178596955677 46713800241098691973858379)
          ·
            refine ⟨70070700361648037960787569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46713800241098691973858379 70070700361648037960787569)
            ·
              refine ⟨52553025271236028470590677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70070700361648037960787569 52553025271236028470590677)
              ·
                refine ⟨1231711529794594417279469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 52553025271236028470590677 1231711529794594417279469)
                ·
                  refine ⟨461891823672972906479801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1231711529794594417279469 461891823672972906479801)
                  ·
                    rfl

theorem cell21_2023945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 7, 3].length) (baseStart_2023945 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2023945 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2023945 prefixEnd_2023945 := by exact prefixLift 2023945
  have htrace : WordTrace (prefixWord ++ tailWord_2023945) baseStart_2023945 baseEnd_2023945 := by
    simpa [prefixWord, tailWord_2023945, baseEnd_2023945] using wordTrace_append hprefix tailTrace_2023945
  have hstable : (prefixWord ++ tailWord_2023945).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2023945).length < 2 ^ (prefixWord ++ tailWord_2023945).sum := by decide
  have hdescent : baseEnd_2023945 < baseStart_2023945 := by decide
  rcases family_descends (prefixWord ++ tailWord_2023945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2023973 : List Nat := [1, 3, 1, 2, 2, 1, 3, 8]
def baseStart_2023973 : Nat := 118140960795 + 2023973 * 2 ^ 59
def prefixEnd_2023973 : Nat := 4983230072969 + 3 ^ 40 * 2023973 * 2
def baseEnd_2023973 : Nat := 153966071218150360004359

theorem tailTrace_2023973 : CollatzResearch.WordTrace tailWord_2023973 prefixEnd_2023973 153966071218150360004359 := by
  unfold tailWord_2023973
  simp only [CollatzResearch.WordTrace]
  refine ⟨73820359896498962913548573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49213573264332641942365715 73820359896498962913548573)
  ·
    refine ⟨27682634961187111092580715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73820359896498962913548573 27682634961187111092580715)
    ·
      refine ⟨41523952441780666638871073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27682634961187111092580715 41523952441780666638871073)
      ·
        refine ⟨31142964331335499979153305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41523952441780666638871073 31142964331335499979153305)
        ·
          refine ⟨23357223248501624984364979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31142964331335499979153305 23357223248501624984364979)
          ·
            refine ⟨35035834872752437476547469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23357223248501624984364979 35035834872752437476547469)
            ·
              refine ⟨13138438077282164053705301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35035834872752437476547469 13138438077282164053705301)
              ·
                refine ⟨153966071218150360004359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13138438077282164053705301 153966071218150360004359)
                ·
                  rfl

theorem cell21_2023973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 8].length) (baseStart_2023973 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2023973 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2023973 prefixEnd_2023973 := by exact prefixLift 2023973
  have htrace : WordTrace (prefixWord ++ tailWord_2023973) baseStart_2023973 baseEnd_2023973 := by
    simpa [prefixWord, tailWord_2023973, baseEnd_2023973] using wordTrace_append hprefix tailTrace_2023973
  have hstable : (prefixWord ++ tailWord_2023973).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2023973).length < 2 ^ (prefixWord ++ tailWord_2023973).sum := by decide
  have hdescent : baseEnd_2023973 < baseStart_2023973 := by decide
  rcases family_descends (prefixWord ++ tailWord_2023973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2024035 : List Nat := [1, 1, 1, 5, 1, 2, 1, 5, 4]
def baseStart_2024035 : Nat := 118140960795 + 2024035 * 2 ^ 59
def prefixEnd_2024035 : Nat := 4983230072969 + 3 ^ 40 * 2024035 * 2
def baseEnd_2024035 : Nat := 461912362899152749979617

theorem tailTrace_2024035 : CollatzResearch.WordTrace tailWord_2024035 prefixEnd_2024035 461912362899152749979617 := by
  unfold tailWord_2024035
  simp only [CollatzResearch.WordTrace]
  refine ⟨73822621222274347502305559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49215080814849565001537039 73822621222274347502305559)
  ·
    refine ⟨110733931833411521253458339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73822621222274347502305559 110733931833411521253458339)
    ·
      refine ⟨166100897750117281880187509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110733931833411521253458339 166100897750117281880187509)
      ·
        refine ⟨15571959164073495176267579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 166100897750117281880187509 15571959164073495176267579)
        ·
          refine ⟨23357938746110242764401369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15571959164073495176267579 23357938746110242764401369)
          ·
            refine ⟨17518454059582682073301027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23357938746110242764401369 17518454059582682073301027)
            ·
              refine ⟨26277681089374023109951541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17518454059582682073301027 26277681089374023109951541)
              ·
                refine ⟨2463532602128814666557957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26277681089374023109951541 2463532602128814666557957)
                ·
                  refine ⟨461912362899152749979617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2463532602128814666557957 461912362899152749979617)
                  ·
                    rfl

theorem cell21_2024035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 5, 4].length) (baseStart_2024035 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2024035 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2024035 prefixEnd_2024035 := by exact prefixLift 2024035
  have htrace : WordTrace (prefixWord ++ tailWord_2024035) baseStart_2024035 baseEnd_2024035 := by
    simpa [prefixWord, tailWord_2024035, baseEnd_2024035] using wordTrace_append hprefix tailTrace_2024035
  have hstable : (prefixWord ++ tailWord_2024035).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2024035).length < 2 ^ (prefixWord ++ tailWord_2024035).sum := by decide
  have hdescent : baseEnd_2024035 < baseStart_2024035 := by decide
  rcases family_descends (prefixWord ++ tailWord_2024035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2024125 : List Nat := [1, 4, 1, 2, 1, 3, 9]
def baseStart_2024125 : Nat := 118140960795 + 2024125 * 2 ^ 59
def prefixEnd_2024125 : Nat := 4983230072969 + 3 ^ 40 * 2024125 * 2
def baseEnd_2024125 : Nat := 51325878013925843719937

theorem tailTrace_2024125 : CollatzResearch.WordTrace tailWord_2024125 prefixEnd_2024125 51325878013925843719937 := by
  unfold tailWord_2024125
  simp only [CollatzResearch.WordTrace]
  refine ⟨73825903791948292873081829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49217269194632195248721219 73825903791948292873081829)
  ·
    refine ⟨13842356960990304913702843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73825903791948292873081829 13842356960990304913702843)
    ·
      refine ⟨20763535441485457370554265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13842356960990304913702843 20763535441485457370554265)
      ·
        refine ⟨15572651581114093027915699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20763535441485457370554265 15572651581114093027915699)
        ·
          refine ⟨23358977371671139541873549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15572651581114093027915699 23358977371671139541873549)
          ·
            refine ⟨8759616514376677328202581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23358977371671139541873549 8759616514376677328202581)
            ·
              refine ⟨51325878013925843719937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8759616514376677328202581 51325878013925843719937)
              ·
                rfl

theorem cell21_2024125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 9].length) (baseStart_2024125 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2024125 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2024125 prefixEnd_2024125 := by exact prefixLift 2024125
  have htrace : WordTrace (prefixWord ++ tailWord_2024125) baseStart_2024125 baseEnd_2024125 := by
    simpa [prefixWord, tailWord_2024125, baseEnd_2024125] using wordTrace_append hprefix tailTrace_2024125
  have hstable : (prefixWord ++ tailWord_2024125).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2024125).length < 2 ^ (prefixWord ++ tailWord_2024125).sum := by decide
  have hdescent : baseEnd_2024125 < baseStart_2024125 := by decide
  rcases family_descends (prefixWord ++ tailWord_2024125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2024142 : List Nat := [4, 1, 1, 1, 3, 3, 2, 6]
def baseStart_2024142 : Nat := 118140960795 + 2024142 * 2 ^ 59
def prefixEnd_2024142 : Nat := 4983230072969 + 3 ^ 40 * 2024142 * 2
def baseEnd_2024142 : Nat := 153978927252314780565355

theorem tailTrace_2024142 : CollatzResearch.WordTrace tailWord_2024142 prefixEnd_2024142 153978927252314780565355 := by
  unfold tailWord_2024142
  simp only [CollatzResearch.WordTrace]
  refine ⟨9228315479110838097056335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49217682555257803184300453 9228315479110838097056335)
  ·
    refine ⟨13842473218666257145584503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9228315479110838097056335 13842473218666257145584503)
    ·
      refine ⟨20763709827999385718376755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13842473218666257145584503 20763709827999385718376755)
      ·
        refine ⟨31145564741999078577565133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20763709827999385718376755 31145564741999078577565133)
        ·
          refine ⟨11679586778249654466586925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31145564741999078577565133 11679586778249654466586925)
          ·
            refine ⟨4379845041843620424970097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11679586778249654466586925 4379845041843620424970097)
            ·
              refine ⟨3284883781382715318727573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4379845041843620424970097 3284883781382715318727573)
              ·
                refine ⟨153978927252314780565355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3284883781382715318727573 153978927252314780565355)
                ·
                  rfl

theorem cell21_2024142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 2, 6].length) (baseStart_2024142 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2024142 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2024142 prefixEnd_2024142 := by exact prefixLift 2024142
  have htrace : WordTrace (prefixWord ++ tailWord_2024142) baseStart_2024142 baseEnd_2024142 := by
    simpa [prefixWord, tailWord_2024142, baseEnd_2024142] using wordTrace_append hprefix tailTrace_2024142
  have hstable : (prefixWord ++ tailWord_2024142).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2024142).length < 2 ^ (prefixWord ++ tailWord_2024142).sum := by decide
  have hdescent : baseEnd_2024142 < baseStart_2024142 := by decide
  rcases family_descends (prefixWord ++ tailWord_2024142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2024201 : List Nat := [1, 2, 1, 1, 3, 2, 5, 6]
def baseStart_2024201 : Nat := 118140960795 + 2024201 * 2 ^ 59
def prefixEnd_2024201 : Nat := 4983230072969 + 3 ^ 40 * 2024201 * 2
def baseEnd_2024201 : Nat := 153983415453591116737537

theorem tailTrace_2024201 : CollatzResearch.WordTrace tailWord_2024201 prefixEnd_2024201 153983415453591116737537 := by
  unfold tailWord_2024201
  simp only [CollatzResearch.WordTrace]
  refine ⟨73828675739672957852848457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49219117159781971901898971 73828675739672957852848457)
  ·
    refine ⟨55371506804754718389636343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73828675739672957852848457 55371506804754718389636343)
    ·
      refine ⟨83057260207132077584454515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55371506804754718389636343 83057260207132077584454515)
      ·
        refine ⟨124585890310698116376681773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83057260207132077584454515 124585890310698116376681773)
        ·
          refine ⟨46719708866511793641255665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124585890310698116376681773 46719708866511793641255665)
          ·
            refine ⟨35039781649883845230941749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46719708866511793641255665 35039781649883845230941749)
            ·
              refine ⟨3284979529676610490400789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35039781649883845230941749 3284979529676610490400789)
              ·
                refine ⟨153983415453591116737537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3284979529676610490400789 153983415453591116737537)
                ·
                  rfl

theorem cell21_2024201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 5, 6].length) (baseStart_2024201 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2024201 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2024201 prefixEnd_2024201 := by exact prefixLift 2024201
  have htrace : WordTrace (prefixWord ++ tailWord_2024201) baseStart_2024201 baseEnd_2024201 := by
    simpa [prefixWord, tailWord_2024201, baseEnd_2024201] using wordTrace_append hprefix tailTrace_2024201
  have hstable : (prefixWord ++ tailWord_2024201).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2024201).length < 2 ^ (prefixWord ++ tailWord_2024201).sum := by decide
  have hdescent : baseEnd_2024201 < baseStart_2024201 := by decide
  rcases family_descends (prefixWord ++ tailWord_2024201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2024218 : List Nat := [3, 1, 1, 3, 2, 1, 5, 5]
def baseStart_2024218 : Nat := 118140960795 + 2024218 * 2 ^ 59
def prefixEnd_2024218 : Nat := 4983230072969 + 3 ^ 40 * 2024218 * 2
def baseEnd_2024218 : Nat := 153984708664128366143081

theorem tailTrace_2024218 : CollatzResearch.WordTrace tailWord_2024218 prefixEnd_2024218 153984708664128366143081 := by
  unfold tailWord_2024218
  simp only [CollatzResearch.WordTrace]
  refine ⟨18457323945152842439054327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49219530520407579837478205 18457323945152842439054327)
  ·
    refine ⟨27685985917729263658581491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18457323945152842439054327 27685985917729263658581491)
    ·
      refine ⟨41528978876593895487872237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27685985917729263658581491 41528978876593895487872237)
      ·
        refine ⟨15573367078722710807952089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41528978876593895487872237 15573367078722710807952089)
        ·
          refine ⟨11680025309042033105964067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15573367078722710807952089 11680025309042033105964067)
          ·
            refine ⟨17520037963563049658946101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11680025309042033105964067 17520037963563049658946101)
            ·
              refine ⟨1642503559084035905526197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17520037963563049658946101 1642503559084035905526197)
              ·
                refine ⟨153984708664128366143081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1642503559084035905526197 153984708664128366143081)
                ·
                  rfl

theorem cell21_2024218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 5, 5].length) (baseStart_2024218 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2024218 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2024218 prefixEnd_2024218 := by exact prefixLift 2024218
  have htrace : WordTrace (prefixWord ++ tailWord_2024218) baseStart_2024218 baseEnd_2024218 := by
    simpa [prefixWord, tailWord_2024218, baseEnd_2024218] using wordTrace_append hprefix tailTrace_2024218
  have hstable : (prefixWord ++ tailWord_2024218).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2024218).length < 2 ^ (prefixWord ++ tailWord_2024218).sum := by decide
  have hdescent : baseEnd_2024218 < baseStart_2024218 := by decide
  rcases family_descends (prefixWord ++ tailWord_2024218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2024232 : List Nat := [2, 1, 5, 1, 1, 1, 1, 2, 7]
def baseStart_2024232 : Nat := 118140960795 + 2024232 * 2 ^ 59
def prefixEnd_2024232 : Nat := 4983230072969 + 3 ^ 40 * 2024232 * 2
def baseEnd_2024232 : Nat := 461957320983124185195881

theorem tailTrace_2024232 : CollatzResearch.WordTrace tailWord_2024232 prefixEnd_2024232 461957320983124185195881 := by
  unfold tailWord_2024232
  simp only [CollatzResearch.WordTrace]
  refine ⟨36914903201280325073613475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49219870935040433431484633 36914903201280325073613475)
  ·
    refine ⟨55372354801920487610420213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36914903201280325073613475 55372354801920487610420213)
    ·
      refine ⟨5191158262680045713476895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 55372354801920487610420213 5191158262680045713476895)
      ·
        refine ⟨7786737394020068570215343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5191158262680045713476895 7786737394020068570215343)
        ·
          refine ⟨11680106091030102855323015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7786737394020068570215343 11680106091030102855323015)
          ·
            refine ⟨17520159136545154282984523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11680106091030102855323015 17520159136545154282984523)
            ·
              refine ⟨26280238704817731424476785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17520159136545154282984523 26280238704817731424476785)
              ·
                refine ⟨19710179028613298568357589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26280238704817731424476785 19710179028613298568357589)
                ·
                  refine ⟨461957320983124185195881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19710179028613298568357589 461957320983124185195881)
                  ·
                    rfl

theorem cell21_2024232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 2, 7].length) (baseStart_2024232 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2024232 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2024232 prefixEnd_2024232 := by exact prefixLift 2024232
  have htrace : WordTrace (prefixWord ++ tailWord_2024232) baseStart_2024232 baseEnd_2024232 := by
    simpa [prefixWord, tailWord_2024232, baseEnd_2024232] using wordTrace_append hprefix tailTrace_2024232
  have hstable : (prefixWord ++ tailWord_2024232).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2024232).length < 2 ^ (prefixWord ++ tailWord_2024232).sum := by decide
  have hdescent : baseEnd_2024232 < baseStart_2024232 := by decide
  rcases family_descends (prefixWord ++ tailWord_2024232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2024269 : List Nat := [1, 6, 1, 2, 3, 1, 2, 5]
def baseStart_2024269 : Nat := 118140960795 + 2024269 * 2 ^ 59
def prefixEnd_2024269 : Nat := 4983230072969 + 3 ^ 40 * 2024269 * 2
def baseEnd_2024269 : Nat := 153988588295740114359713

theorem tailTrace_2024269 : CollatzResearch.WordTrace tailWord_2024269 prefixEnd_2024269 153988588295740114359713 := by
  unfold tailWord_2024269
  simp only [CollatzResearch.WordTrace]
  refine ⟨73831155903426605466323861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49220770602284403644215907 73831155903426605466323861)
  ·
    refine ⟨3460835432973122131233931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 73831155903426605466323861 3460835432973122131233931)
    ·
      refine ⟨5191253149459683196850897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3460835432973122131233931 5191253149459683196850897)
      ·
        refine ⟨3893439862094762397638173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5191253149459683196850897 3893439862094762397638173)
        ·
          refine ⟨1460039948285535899114315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3893439862094762397638173 1460039948285535899114315)
          ·
            refine ⟨2190059922428303848671473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1460039948285535899114315 2190059922428303848671473)
            ·
              refine ⟨1642544941821227886503605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2190059922428303848671473 1642544941821227886503605)
              ·
                refine ⟨153988588295740114359713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1642544941821227886503605 153988588295740114359713)
                ·
                  rfl

theorem cell21_2024269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 2, 5].length) (baseStart_2024269 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2024269 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2024269 prefixEnd_2024269 := by exact prefixLift 2024269
  have htrace : WordTrace (prefixWord ++ tailWord_2024269) baseStart_2024269 baseEnd_2024269 := by
    simpa [prefixWord, tailWord_2024269, baseEnd_2024269] using wordTrace_append hprefix tailTrace_2024269
  have hstable : (prefixWord ++ tailWord_2024269).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2024269).length < 2 ^ (prefixWord ++ tailWord_2024269).sum := by decide
  have hdescent : baseEnd_2024269 < baseStart_2024269 := by decide
  rcases family_descends (prefixWord ++ tailWord_2024269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2024277 : List Nat := [1, 3, 2, 2, 2, 1, 3, 7]
def baseStart_2024277 : Nat := 118140960795 + 2024277 * 2 ^ 59
def prefixEnd_2024277 : Nat := 4983230072969 + 3 ^ 40 * 2024277 * 2
def baseEnd_2024277 : Nat := 153989196865404702315263

theorem tailTrace_2024277 : CollatzResearch.WordTrace tailWord_2024277 prefixEnd_2024277 153989196865404702315263 := by
  unfold tailWord_2024277
  simp only [CollatzResearch.WordTrace]
  refine ⟨73831447687397622832615085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49220965124931748555076723 73831447687397622832615085)
  ·
    refine ⟨27686792882774108562230657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73831447687397622832615085 27686792882774108562230657)
    ·
      refine ⟨20765094662080581421672993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27686792882774108562230657 20765094662080581421672993)
      ·
        refine ⟨15573820996560436066254745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20765094662080581421672993 15573820996560436066254745)
        ·
          refine ⟨11680365747420327049691059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15573820996560436066254745 11680365747420327049691059)
          ·
            refine ⟨17520548621130490574536589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11680365747420327049691059 17520548621130490574536589)
            ·
              refine ⟨6570205732923933965451221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17520548621130490574536589 6570205732923933965451221)
              ·
                refine ⟨153989196865404702315263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6570205732923933965451221 153989196865404702315263)
                ·
                  rfl

theorem cell21_2024277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 3, 7].length) (baseStart_2024277 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2024277 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2024277 prefixEnd_2024277 := by exact prefixLift 2024277
  have htrace : WordTrace (prefixWord ++ tailWord_2024277) baseStart_2024277 baseEnd_2024277 := by
    simpa [prefixWord, tailWord_2024277, baseEnd_2024277] using wordTrace_append hprefix tailTrace_2024277
  have hstable : (prefixWord ++ tailWord_2024277).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2024277).length < 2 ^ (prefixWord ++ tailWord_2024277).sum := by decide
  have hdescent : baseEnd_2024277 < baseStart_2024277 := by decide
  rcases family_descends (prefixWord ++ tailWord_2024277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2024353 : List Nat := [1, 2, 3, 4, 1, 10]
def baseStart_2024353 : Nat := 118140960795 + 2024353 * 2 ^ 59
def prefixEnd_2024353 : Nat := 4983230072969 + 3 ^ 40 * 2024353 * 2
def baseEnd_2024353 : Nat := 17110553141913143099221

theorem tailTrace_2024353 : CollatzResearch.WordTrace tailWord_2024353 prefixEnd_2024353 17110553141913143099221 := by
  unfold tailWord_2024353
  simp only [CollatzResearch.WordTrace]
  refine ⟨73834219635122287812381713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49222813090081525208254475 73834219635122287812381713)
  ·
    refine ⟨55375664726341715859286285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73834219635122287812381713 55375664726341715859286285)
    ·
      refine ⟨20765874272378143447232357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55375664726341715859286285 20765874272378143447232357)
      ·
        refine ⟨3893601426070901896356067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20765874272378143447232357 3893601426070901896356067)
        ·
          refine ⟨5840402139106352844534101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3893601426070901896356067 5840402139106352844534101)
          ·
            refine ⟨17110553141913143099221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5840402139106352844534101 17110553141913143099221)
            ·
              rfl

theorem cell21_2024353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 10].length) (baseStart_2024353 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2024353 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2024353 prefixEnd_2024353 := by exact prefixLift 2024353
  have htrace : WordTrace (prefixWord ++ tailWord_2024353) baseStart_2024353 baseEnd_2024353 := by
    simpa [prefixWord, tailWord_2024353, baseEnd_2024353] using wordTrace_append hprefix tailTrace_2024353
  have hstable : (prefixWord ++ tailWord_2024353).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2024353).length < 2 ^ (prefixWord ++ tailWord_2024353).sum := by decide
  have hdescent : baseEnd_2024353 < baseStart_2024353 := by decide
  rcases family_descends (prefixWord ++ tailWord_2024353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2024384 : List Nat := [2, 1, 1, 2, 3, 4, 1, 2, 5]
def baseStart_2024384 : Nat := 118140960795 + 2024384 * 2 ^ 59
def prefixEnd_2024384 : Nat := 4983230072969 + 3 ^ 40 * 2024384 * 2
def baseEnd_2024384 : Nat := 461992009454005698662237

theorem tailTrace_2024384 : CollatzResearch.WordTrace tailWord_2024384 prefixEnd_2024384 461992009454005698662237 := by
  unfold tailWord_2024384
  simp only [CollatzResearch.WordTrace]
  refine ⟨36917675149004990053380103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49223566865339986737840137 36917675149004990053380103)
  ·
    refine ⟨55376512723507485080070155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36917675149004990053380103 55376512723507485080070155)
    ·
      refine ⟨83064769085261227620105233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55376512723507485080070155 83064769085261227620105233)
      ·
        refine ⟨62298576813945920715078925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83064769085261227620105233 62298576813945920715078925)
        ·
          refine ⟨23361966305229720268154597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62298576813945920715078925 23361966305229720268154597)
          ·
            refine ⟨4380368682230572550278987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23361966305229720268154597 4380368682230572550278987)
            ·
              refine ⟨6570553023345858825418481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4380368682230572550278987 6570553023345858825418481)
              ·
                refine ⟨4927914767509394119063861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6570553023345858825418481 4927914767509394119063861)
                ·
                  refine ⟨461992009454005698662237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4927914767509394119063861 461992009454005698662237)
                  ·
                    rfl

theorem cell21_2024384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 1, 2, 5].length) (baseStart_2024384 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2024384 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2024384 prefixEnd_2024384 := by exact prefixLift 2024384
  have htrace : WordTrace (prefixWord ++ tailWord_2024384) baseStart_2024384 baseEnd_2024384 := by
    simpa [prefixWord, tailWord_2024384, baseEnd_2024384] using wordTrace_append hprefix tailTrace_2024384
  have hstable : (prefixWord ++ tailWord_2024384).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2024384).length < 2 ^ (prefixWord ++ tailWord_2024384).sum := by decide
  have hdescent : baseEnd_2024384 < baseStart_2024384 := by decide
  rcases family_descends (prefixWord ++ tailWord_2024384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2024401 : List Nat := [1, 2, 2, 1, 2, 1, 6, 3, 3]
def baseStart_2024401 : Nat := 118140960795 + 2024401 * 2 ^ 59
def prefixEnd_2024401 : Nat := 4983230072969 + 3 ^ 40 * 2024401 * 2
def baseEnd_2024401 : Nat := 461995889085617446878869

theorem tailTrace_2024401 : CollatzResearch.WordTrace tailWord_2024401 prefixEnd_2024401 461995889085617446878869 := by
  unfold tailWord_2024401
  simp only [CollatzResearch.WordTrace]
  refine ⟨73835970338948392010129057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49223980225965594673419371 73835970338948392010129057)
  ·
    refine ⟨55376977754211294007596793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73835970338948392010129057 55376977754211294007596793)
    ·
      refine ⟨41532733315658470505697595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55376977754211294007596793 41532733315658470505697595)
      ·
        refine ⟨62299099973487705758546393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41532733315658470505697595 62299099973487705758546393)
        ·
          refine ⟨46724324980115779318909795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62299099973487705758546393 46724324980115779318909795)
          ·
            refine ⟨70086487470173668978364693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46724324980115779318909795 70086487470173668978364693)
            ·
              refine ⟨3285304100164390733360845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 70086487470173668978364693 3285304100164390733360845)
              ·
                refine ⟨1231989037561646525010317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3285304100164390733360845 1231989037561646525010317)
                ·
                  refine ⟨461995889085617446878869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1231989037561646525010317 461995889085617446878869)
                  ·
                    rfl

theorem cell21_2024401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 6, 3, 3].length) (baseStart_2024401 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2024401 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2024401 prefixEnd_2024401 := by exact prefixLift 2024401
  have htrace : WordTrace (prefixWord ++ tailWord_2024401) baseStart_2024401 baseEnd_2024401 := by
    simpa [prefixWord, tailWord_2024401, baseEnd_2024401] using wordTrace_append hprefix tailTrace_2024401
  have hstable : (prefixWord ++ tailWord_2024401).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2024401).length < 2 ^ (prefixWord ++ tailWord_2024401).sum := by decide
  have hdescent : baseEnd_2024401 < baseStart_2024401 := by decide
  rcases family_descends (prefixWord ++ tailWord_2024401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2024415 : List Nat := [1, 1, 2, 3, 5, 1, 1, 1, 6]
def baseStart_2024415 : Nat := 118140960795 + 2024415 * 2 ^ 59
def prefixEnd_2024415 : Nat := 4983230072969 + 3 ^ 40 * 2024415 * 2
def baseEnd_2024415 : Nat := 461999084076356533645507

theorem tailTrace_2024415 : CollatzResearch.WordTrace tailWord_2024415 prefixEnd_2024415 461999084076356533645507 := by
  unfold tailWord_2024415
  simp only [CollatzResearch.WordTrace]
  refine ⟨73836480960897672401138699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49224320640598448267425799 73836480960897672401138699)
  ·
    refine ⟨110754721441346508601708049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73836480960897672401138699 110754721441346508601708049)
    ·
      refine ⟨83066041081009881451281037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110754721441346508601708049 83066041081009881451281037)
      ·
        refine ⟨31149765405378705544230389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83066041081009881451281037 31149765405378705544230389)
        ·
          refine ⟨2920290506754253644771599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31149765405378705544230389 2920290506754253644771599)
          ·
            refine ⟨4380435760131380467157399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2920290506754253644771599 4380435760131380467157399)
            ·
              refine ⟨6570653640197070700736099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4380435760131380467157399 6570653640197070700736099)
              ·
                refine ⟨9855980460295606051104149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6570653640197070700736099 9855980460295606051104149)
                ·
                  refine ⟨461999084076356533645507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9855980460295606051104149 461999084076356533645507)
                  ·
                    rfl

theorem cell21_2024415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 1, 1, 6].length) (baseStart_2024415 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2024415 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2024415 prefixEnd_2024415 := by exact prefixLift 2024415
  have htrace : WordTrace (prefixWord ++ tailWord_2024415) baseStart_2024415 baseEnd_2024415 := by
    simpa [prefixWord, tailWord_2024415, baseEnd_2024415] using wordTrace_append hprefix tailTrace_2024415
  have hstable : (prefixWord ++ tailWord_2024415).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2024415).length < 2 ^ (prefixWord ++ tailWord_2024415).sum := by decide
  have hdescent : baseEnd_2024415 < baseStart_2024415 := by decide
  rcases family_descends (prefixWord ++ tailWord_2024415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2024418 : List Nat := [3, 3, 3, 1, 1, 2, 2, 1, 5]
def baseStart_2024418 : Nat := 118140960795 + 2024418 * 2 ^ 59
def prefixEnd_2024418 : Nat := 4983230072969 + 3 ^ 40 * 2024418 * 2
def baseEnd_2024418 : Nat := 461999768717229195095501

theorem tailTrace_2024418 : CollatzResearch.WordTrace tailWord_2024418 prefixEnd_2024418 461999768717229195095501 := by
  unfold tailWord_2024418
  simp only [CollatzResearch.WordTrace]
  refine ⟨18459147594971700978374477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49224393586591202608998605 18459147594971700978374477)
  ·
    refine ⟨6922180348114387866890429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18459147594971700978374477 6922180348114387866890429)
    ·
      refine ⟨2595817630542895450083911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6922180348114387866890429 2595817630542895450083911)
      ·
        refine ⟨3893726445814343175125867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2595817630542895450083911 3893726445814343175125867)
        ·
          refine ⟨5840589668721514762688801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3893726445814343175125867 5840589668721514762688801)
          ·
            refine ⟨4380442251541136072016601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5840589668721514762688801 4380442251541136072016601)
            ·
              refine ⟨3285331688655852054012451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4380442251541136072016601 3285331688655852054012451)
              ·
                refine ⟨4927997532983778081018677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3285331688655852054012451 4927997532983778081018677)
                ·
                  refine ⟨461999768717229195095501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4927997532983778081018677 461999768717229195095501)
                  ·
                    rfl

theorem cell21_2024418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 2, 1, 5].length) (baseStart_2024418 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2024418 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2024418 prefixEnd_2024418 := by exact prefixLift 2024418
  have htrace : WordTrace (prefixWord ++ tailWord_2024418) baseStart_2024418 baseEnd_2024418 := by
    simpa [prefixWord, tailWord_2024418, baseEnd_2024418] using wordTrace_append hprefix tailTrace_2024418
  have hstable : (prefixWord ++ tailWord_2024418).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2024418).length < 2 ^ (prefixWord ++ tailWord_2024418).sum := by decide
  have hdescent : baseEnd_2024418 < baseStart_2024418 := by decide
  rcases family_descends (prefixWord ++ tailWord_2024418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2024474 : List Nat := [3, 1, 1, 3, 1, 2, 1, 3, 6]
def baseStart_2024474 : Nat := 118140960795 + 2024474 * 2 ^ 59
def prefixEnd_2024474 : Nat := 4983230072969 + 3 ^ 40 * 2024474 * 2
def baseEnd_2024474 : Nat := 462012548680185542162053

theorem tailTrace_2024474 : CollatzResearch.WordTrace tailWord_2024474 prefixEnd_2024474 462012548680185542162053 := by
  unfold tailWord_2024474
  simp only [CollatzResearch.WordTrace]
  refine ⟨18459658216920981369384119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49225755245122616985024317 18459658216920981369384119)
  ·
    refine ⟨27689487325381472054076179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18459658216920981369384119 27689487325381472054076179)
    ·
      refine ⟨41534230988072208081114269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27689487325381472054076179 41534230988072208081114269)
      ·
        refine ⟨15575336620527078030417851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41534230988072208081114269 15575336620527078030417851)
        ·
          refine ⟨23363004930790617045626777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15575336620527078030417851 23363004930790617045626777)
          ·
            refine ⟨17522253698092962784220083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23363004930790617045626777 17522253698092962784220083)
            ·
              refine ⟨26283380547139444176330125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17522253698092962784220083 26283380547139444176330125)
              ·
                refine ⟨9856267705177291566123797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26283380547139444176330125 9856267705177291566123797)
                ·
                  refine ⟨462012548680185542162053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9856267705177291566123797 462012548680185542162053)
                  ·
                    rfl

theorem cell21_2024474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 3, 6].length) (baseStart_2024474 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2024474 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2024474 prefixEnd_2024474 := by exact prefixLift 2024474
  have htrace : WordTrace (prefixWord ++ tailWord_2024474) baseStart_2024474 baseEnd_2024474 := by
    simpa [prefixWord, tailWord_2024474, baseEnd_2024474] using wordTrace_append hprefix tailTrace_2024474
  have hstable : (prefixWord ++ tailWord_2024474).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2024474).length < 2 ^ (prefixWord ++ tailWord_2024474).sum := by decide
  have hdescent : baseEnd_2024474 < baseStart_2024474 := by decide
  rcases family_descends (prefixWord ++ tailWord_2024474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2024505 : List Nat := [1, 2, 1, 5, 2, 1, 2, 7]
def baseStart_2024505 : Nat := 118140960795 + 2024505 * 2 ^ 59
def prefixEnd_2024505 : Nat := 4983230072969 + 3 ^ 40 * 2024505 * 2
def baseEnd_2024505 : Nat := 154006541100845459048441

theorem tailTrace_2024505 : CollatzResearch.WordTrace tailWord_2024505 prefixEnd_2024505 154006541100845459048441 := by
  unfold tailWord_2024505
  simp only [CollatzResearch.WordTrace]
  refine ⟨73839763530571617771914969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49226509020381078514609979 73839763530571617771914969)
  ·
    refine ⟨55379822647928713328936227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73839763530571617771914969 55379822647928713328936227)
    ·
      refine ⟨83069733971893069993404341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55379822647928713328936227 83069733971893069993404341)
      ·
        refine ⟨7787787559864975311881657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 83069733971893069993404341 7787787559864975311881657)
        ·
          refine ⟨5840840669898731483911243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7787787559864975311881657 5840840669898731483911243)
          ·
            refine ⟨8761261004848097225866865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5840840669898731483911243 8761261004848097225866865)
            ·
              refine ⟨6570945753636072919400149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8761261004848097225866865 6570945753636072919400149)
              ·
                refine ⟨154006541100845459048441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6570945753636072919400149 154006541100845459048441)
                ·
                  rfl

theorem cell21_2024505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 2, 7].length) (baseStart_2024505 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2024505 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2024505 prefixEnd_2024505 := by exact prefixLift 2024505
  have htrace : WordTrace (prefixWord ++ tailWord_2024505) baseStart_2024505 baseEnd_2024505 := by
    simpa [prefixWord, tailWord_2024505, baseEnd_2024505] using wordTrace_append hprefix tailTrace_2024505
  have hstable : (prefixWord ++ tailWord_2024505).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2024505).length < 2 ^ (prefixWord ++ tailWord_2024505).sum := by decide
  have hdescent : baseEnd_2024505 < baseStart_2024505 := by decide
  rcases family_descends (prefixWord ++ tailWord_2024505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
