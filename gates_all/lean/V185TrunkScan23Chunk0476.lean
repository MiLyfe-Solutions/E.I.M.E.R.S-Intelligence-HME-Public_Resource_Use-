import V185TrunkScan23Chunk0475

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2814809 : List Nat := [1, 2, 1, 2, 2, 4, 1, 2, 1, 5, 2]
def baseStart_2814809 : Nat := 118140960795 + 2814809 * 2 ^ 59
def prefixEnd_2814809 : Nat := 4983230072969 + 3 ^ 40 * 2814809 * 2
def baseEnd_2814809 : Nat := 1445349967601582780542435

theorem tailTrace_2814809 : CollatzResearch.WordTrace tailWord_2814809 prefixEnd_2814809 1445349967601582780542435 := by
  unfold tailWord_2814809
  simp only [CollatzResearch.WordTrace]
  refine ⟨102664518459435198949351481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68443012306290132632900987 102664518459435198949351481)
  ·
    refine ⟨76998388844576399212013611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102664518459435198949351481 76998388844576399212013611)
    ·
      refine ⟨115497583266864598818020417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76998388844576399212013611 115497583266864598818020417)
      ·
        refine ⟨86623187450148449113515313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115497583266864598818020417 86623187450148449113515313)
        ·
          refine ⟨64967390587611336835136485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86623187450148449113515313 64967390587611336835136485)
          ·
            refine ⟨12181385735177125656588091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 64967390587611336835136485 12181385735177125656588091)
            ·
              refine ⟨18272078602765688484882137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12181385735177125656588091 18272078602765688484882137)
              ·
                refine ⟨13704058952074266363661603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18272078602765688484882137 13704058952074266363661603)
                ·
                  refine ⟨20556088428111399545492405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13704058952074266363661603 20556088428111399545492405)
                  ·
                    refine ⟨1927133290135443707389913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 20556088428111399545492405 1927133290135443707389913)
                    ·
                      refine ⟨1445349967601582780542435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1927133290135443707389913 1445349967601582780542435)
                      ·
                        rfl

theorem cell23_2814809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 2, 1, 5, 2].length) (baseStart_2814809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2814809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2814809 prefixEnd_2814809 := by exact prefixLift 2814809
  have htrace : WordTrace (prefixWord ++ tailWord_2814809) baseStart_2814809 baseEnd_2814809 := by
    simpa [prefixWord, tailWord_2814809, baseEnd_2814809] using wordTrace_append hprefix tailTrace_2814809
  have hstable : (prefixWord ++ tailWord_2814809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2814809).length < 2 ^ (prefixWord ++ tailWord_2814809).sum := by decide
  have hdescent : baseEnd_2814809 < baseStart_2814809 := by decide
  rcases family_descends (prefixWord ++ tailWord_2814809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2814819 : List Nat := [1, 1, 1, 5, 3, 1, 1, 4, 1, 5]
def baseStart_2814819 : Nat := 118140960795 + 2814819 * 2 ^ 59
def prefixEnd_2814819 : Nat := 4983230072969 + 3 ^ 40 * 2814819 * 2
def baseEnd_2814819 : Nat := 481785034136042580472463

theorem tailTrace_2814819 : CollatzResearch.WordTrace tailWord_2814819 prefixEnd_2814819 481785034136042580472463 := by
  unfold tailWord_2814819
  simp only [CollatzResearch.WordTrace]
  refine ⟨102664883189398970657215511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68443255459599313771477007 102664883189398970657215511)
  ·
    refine ⟨153997324784098455985823267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102664883189398970657215511 153997324784098455985823267)
    ·
      refine ⟨230995987176147683978734901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153997324784098455985823267 230995987176147683978734901)
      ·
        refine ⟨21655873797763845373006397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 230995987176147683978734901 21655873797763845373006397)
        ·
          refine ⟨8120952674161442014877399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21655873797763845373006397 8120952674161442014877399)
          ·
            refine ⟨12181429011242163022316099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8120952674161442014877399 12181429011242163022316099)
            ·
              refine ⟨18272143516863244533474149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12181429011242163022316099 18272143516863244533474149)
              ·
                refine ⟨3426026909411858350026403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18272143516863244533474149 3426026909411858350026403)
                ·
                  refine ⟨5139040364117787525039605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3426026909411858350026403 5139040364117787525039605)
                  ·
                    refine ⟨481785034136042580472463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5139040364117787525039605 481785034136042580472463)
                    ·
                      rfl

theorem cell23_2814819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 4, 1, 5].length) (baseStart_2814819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2814819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2814819 prefixEnd_2814819 := by exact prefixLift 2814819
  have htrace : WordTrace (prefixWord ++ tailWord_2814819) baseStart_2814819 baseEnd_2814819 := by
    simpa [prefixWord, tailWord_2814819, baseEnd_2814819] using wordTrace_append hprefix tailTrace_2814819
  have hstable : (prefixWord ++ tailWord_2814819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2814819).length < 2 ^ (prefixWord ++ tailWord_2814819).sum := by decide
  have hdescent : baseEnd_2814819 < baseStart_2814819 := by decide
  rcases family_descends (prefixWord ++ tailWord_2814819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2814832 : List Nat := [2, 1, 1, 1, 4, 1, 2, 4, 1, 6]
def baseStart_2814832 : Nat := 118140960795 + 2814832 * 2 ^ 59
def prefixEnd_2814832 : Nat := 4983230072969 + 3 ^ 40 * 2814832 * 2
def baseEnd_2814832 : Nat := 481787259218878730184943

theorem tailTrace_2814832 : CollatzResearch.WordTrace tailWord_2814832 prefixEnd_2814832 481787259218878730184943 := by
  unfold tailWord_2814832
  simp only [CollatzResearch.WordTrace]
  refine ⟨51332678669175936938719375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68443571558901249251625833 51332678669175936938719375)
  ·
    refine ⟨76999018003763905408079063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51332678669175936938719375 76999018003763905408079063)
    ·
      refine ⟨115498527005645858112118595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76999018003763905408079063 115498527005645858112118595)
      ·
        refine ⟨173247790508468787168177893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115498527005645858112118595 173247790508468787168177893)
        ·
          refine ⟨32483960720337897594033355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 173247790508468787168177893 32483960720337897594033355)
          ·
            refine ⟨48725941080506846391050033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32483960720337897594033355 48725941080506846391050033)
            ·
              refine ⟨36544455810380134793287525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48725941080506846391050033 36544455810380134793287525)
              ·
                refine ⟨6852085464446275273741411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36544455810380134793287525 6852085464446275273741411)
                ·
                  refine ⟨10278128196669412910612117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6852085464446275273741411 10278128196669412910612117)
                  ·
                    refine ⟨481787259218878730184943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10278128196669412910612117 481787259218878730184943)
                    ·
                      rfl

theorem cell23_2814832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 4, 1, 6].length) (baseStart_2814832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2814832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2814832 prefixEnd_2814832 := by exact prefixLift 2814832
  have htrace : WordTrace (prefixWord ++ tailWord_2814832) baseStart_2814832 baseEnd_2814832 := by
    simpa [prefixWord, tailWord_2814832, baseEnd_2814832] using wordTrace_append hprefix tailTrace_2814832
  have hstable : (prefixWord ++ tailWord_2814832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2814832).length < 2 ^ (prefixWord ++ tailWord_2814832).sum := by decide
  have hdescent : baseEnd_2814832 < baseStart_2814832 := by decide
  rcases family_descends (prefixWord ++ tailWord_2814832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2814833 : List Nat := [1, 2, 2, 2, 1, 4, 3, 3, 1, 1, 3]
def baseStart_2814833 : Nat := 118140960795 + 2814833 * 2 ^ 59
def prefixEnd_2814833 : Nat := 4983230072969 + 3 ^ 40 * 2814833 * 2
def baseEnd_2814833 : Nat := 1445362291137290686642325

theorem tailTrace_2814833 : CollatzResearch.WordTrace tailWord_2814833 prefixEnd_2814833 1445362291137290686642325 := by
  unfold tailWord_2814833
  simp only [CollatzResearch.WordTrace]
  refine ⟨102665393811348251048225153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68443595874232167365483435 102665393811348251048225153)
  ·
    refine ⟨76999045358511188286168865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102665393811348251048225153 76999045358511188286168865)
    ·
      refine ⟨57749284018883391214626649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76999045358511188286168865 57749284018883391214626649)
      ·
        refine ⟨43311963014162543410969987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57749284018883391214626649 43311963014162543410969987)
        ·
          refine ⟨64967944521243815116454981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43311963014162543410969987 64967944521243815116454981)
          ·
            refine ⟨12181489597733215334335309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 64967944521243815116454981 12181489597733215334335309)
            ·
              refine ⟨4568058599149955750375741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12181489597733215334335309 4568058599149955750375741)
              ·
                refine ⟨1713021974681233406390903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4568058599149955750375741 1713021974681233406390903)
                ·
                  refine ⟨2569532962021850109586355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1713021974681233406390903 2569532962021850109586355)
                  ·
                    refine ⟨3854299443032775164379533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2569532962021850109586355 3854299443032775164379533)
                    ·
                      refine ⟨1445362291137290686642325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3854299443032775164379533 1445362291137290686642325)
                      ·
                        rfl

theorem cell23_2814833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 3, 3, 1, 1, 3].length) (baseStart_2814833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2814833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2814833 prefixEnd_2814833 := by exact prefixLift 2814833
  have htrace : WordTrace (prefixWord ++ tailWord_2814833) baseStart_2814833 baseEnd_2814833 := by
    simpa [prefixWord, tailWord_2814833, baseEnd_2814833] using wordTrace_append hprefix tailTrace_2814833
  have hstable : (prefixWord ++ tailWord_2814833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2814833).length < 2 ^ (prefixWord ++ tailWord_2814833).sum := by decide
  have hdescent : baseEnd_2814833 < baseStart_2814833 := by decide
  rcases family_descends (prefixWord ++ tailWord_2814833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2814870 : List Nat := [5, 3, 1, 1, 1, 1, 3, 2, 1, 5]
def baseStart_2814870 : Nat := 118140960795 + 2814870 * 2 ^ 59
def prefixEnd_2814870 : Nat := 4983230072969 + 3 ^ 40 * 2814870 * 2
def baseEnd_2814870 : Nat := 481793763307169013959885

theorem tailTrace_2814870 : CollatzResearch.WordTrace tailWord_2814870 prefixEnd_2814870 481793763307169013959885 := by
  unfold tailWord_2814870
  simp only [CollatzResearch.WordTrace]
  refine ⟨6416671457013387897957629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 68444495541476137578214709 6416671457013387897957629)
  ·
    refine ⟨2406251796380020461734111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6416671457013387897957629 2406251796380020461734111)
    ·
      refine ⟨3609377694570030692601167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2406251796380020461734111 3609377694570030692601167)
      ·
        refine ⟨5414066541855046038901751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3609377694570030692601167 5414066541855046038901751)
        ·
          refine ⟨8121099812782569058352627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5414066541855046038901751 8121099812782569058352627)
          ·
            refine ⟨12181649719173853587528941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8121099812782569058352627 12181649719173853587528941)
            ·
              refine ⟨4568118644690195095323353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12181649719173853587528941 4568118644690195095323353)
              ·
                refine ⟨3426088983517646321492515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4568118644690195095323353 3426088983517646321492515)
                ·
                  refine ⟨5139133475276469482238773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3426088983517646321492515 5139133475276469482238773)
                  ·
                    refine ⟨481793763307169013959885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5139133475276469482238773 481793763307169013959885)
                    ·
                      rfl

theorem cell23_2814870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 3, 2, 1, 5].length) (baseStart_2814870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2814870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2814870 prefixEnd_2814870 := by exact prefixLift 2814870
  have htrace : WordTrace (prefixWord ++ tailWord_2814870) baseStart_2814870 baseEnd_2814870 := by
    simpa [prefixWord, tailWord_2814870, baseEnd_2814870] using wordTrace_append hprefix tailTrace_2814870
  have hstable : (prefixWord ++ tailWord_2814870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2814870).length < 2 ^ (prefixWord ++ tailWord_2814870).sum := by decide
  have hdescent : baseEnd_2814870 < baseStart_2814870 := by decide
  rcases family_descends (prefixWord ++ tailWord_2814870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2814889 : List Nat := [1, 2, 1, 1, 1, 1, 7, 2, 1, 3, 3]
def baseStart_2814889 : Nat := 118140960795 + 2814889 * 2 ^ 59
def prefixEnd_2814889 : Nat := 4983230072969 + 3 ^ 40 * 2814889 * 2
def baseEnd_2814889 : Nat := 1445391046053942467542067

theorem tailTrace_2814889 : CollatzResearch.WordTrace tailWord_2814889 prefixEnd_2814889 1445391046053942467542067 := by
  unfold tailWord_2814889
  simp only [CollatzResearch.WordTrace]
  refine ⟨102667436299145372612263721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68444957532763581741509147 102667436299145372612263721)
  ·
    refine ⟨77000577224359029459197791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102667436299145372612263721 77000577224359029459197791)
    ·
      refine ⟨115500865836538544188796687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77000577224359029459197791 115500865836538544188796687)
      ·
        refine ⟨173251298754807816283195031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115500865836538544188796687 173251298754807816283195031)
        ·
          refine ⟨259876948132211724424792547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173251298754807816283195031 259876948132211724424792547)
          ·
            refine ⟨389815422198317586637188821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 259876948132211724424792547 389815422198317586637188821)
            ·
              refine ⟨9136298957773068436809113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 389815422198317586637188821 9136298957773068436809113)
              ·
                refine ⟨6852224218329801327606835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9136298957773068436809113 6852224218329801327606835)
                ·
                  refine ⟨10278336327494701991410253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6852224218329801327606835 10278336327494701991410253)
                  ·
                    refine ⟨3854376122810513246778845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10278336327494701991410253 3854376122810513246778845)
                    ·
                      refine ⟨1445391046053942467542067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3854376122810513246778845 1445391046053942467542067)
                      ·
                        rfl

theorem cell23_2814889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 7, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 7, 2, 1, 3, 3].length) (baseStart_2814889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2814889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2814889 prefixEnd_2814889 := by exact prefixLift 2814889
  have htrace : WordTrace (prefixWord ++ tailWord_2814889) baseStart_2814889 baseEnd_2814889 := by
    simpa [prefixWord, tailWord_2814889, baseEnd_2814889] using wordTrace_append hprefix tailTrace_2814889
  have hstable : (prefixWord ++ tailWord_2814889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2814889).length < 2 ^ (prefixWord ++ tailWord_2814889).sum := by decide
  have hdescent : baseEnd_2814889 < baseStart_2814889 := by decide
  rcases family_descends (prefixWord ++ tailWord_2814889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2814900 : List Nat := [2, 5, 2, 1, 1, 2, 2, 2, 2, 4]
def baseStart_2814900 : Nat := 118140960795 + 2814900 * 2 ^ 59
def prefixEnd_2814900 : Nat := 4983230072969 + 3 ^ 40 * 2814900 * 2
def baseEnd_2814900 : Nat := 481798898113713974834839

theorem tailTrace_2814900 : CollatzResearch.WordTrace tailWord_2814900 prefixEnd_2814900 481798898113713974834839 := by
  unfold tailWord_2814900
  simp only [CollatzResearch.WordTrace]
  refine ⟨51333918751052760745457077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68445225001403680993942769 51333918751052760745457077)
  ·
    refine ⟨4812554882911196319886601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 51333918751052760745457077 4812554882911196319886601)
    ·
      refine ⟨3609416162183397239914951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4812554882911196319886601 3609416162183397239914951)
      ·
        refine ⟨5414124243275095859872427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3609416162183397239914951 5414124243275095859872427)
        ·
          refine ⟨8121186364912643789808641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5414124243275095859872427 8121186364912643789808641)
          ·
            refine ⟨6090889773684482842356481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8121186364912643789808641 6090889773684482842356481)
            ·
              refine ⟨4568167330263362131767361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6090889773684482842356481 4568167330263362131767361)
              ·
                refine ⟨3426125497697521598825521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4568167330263362131767361 3426125497697521598825521)
                ·
                  refine ⟨2569594123273141199119141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3426125497697521598825521 2569594123273141199119141)
                  ·
                    refine ⟨481798898113713974834839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2569594123273141199119141 481798898113713974834839)
                    ·
                      rfl

theorem cell23_2814900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 2, 2, 2, 4].length) (baseStart_2814900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2814900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2814900 prefixEnd_2814900 := by exact prefixLift 2814900
  have htrace : WordTrace (prefixWord ++ tailWord_2814900) baseStart_2814900 baseEnd_2814900 := by
    simpa [prefixWord, tailWord_2814900, baseEnd_2814900] using wordTrace_append hprefix tailTrace_2814900
  have hstable : (prefixWord ++ tailWord_2814900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2814900).length < 2 ^ (prefixWord ++ tailWord_2814900).sum := by decide
  have hdescent : baseEnd_2814900 < baseStart_2814900 := by decide
  rcases family_descends (prefixWord ++ tailWord_2814900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2814959 : List Nat := [1, 1, 2, 1, 4, 3, 1, 2, 2, 2, 4]
def baseStart_2814959 : Nat := 118140960795 + 2814959 * 2 ^ 59
def prefixEnd_2814959 : Nat := 4983230072969 + 3 ^ 40 * 2814959 * 2
def baseEnd_2814959 : Nat := 1445426989699757193666745

theorem tailTrace_2814959 : CollatzResearch.WordTrace tailWord_2814959 prefixEnd_2814959 1445426989699757193666745 := by
  unfold tailWord_2814959
  simp only [CollatzResearch.WordTrace]
  refine ⟨102669989408891774567311931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68446659605927849711541287 102669989408891774567311931)
  ·
    refine ⟨154004984113337661850967897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102669989408891774567311931 154004984113337661850967897)
    ·
      refine ⟨115503738085003246388225923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154004984113337661850967897 115503738085003246388225923)
      ·
        refine ⟨173255607127504869582338885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115503738085003246388225923 173255607127504869582338885)
        ·
          refine ⟨32485426336407163046688541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 173255607127504869582338885 32485426336407163046688541)
          ·
            refine ⟨12182034876152686142508203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32485426336407163046688541 12182034876152686142508203)
            ·
              refine ⟨18273052314229029213762305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12182034876152686142508203 18273052314229029213762305)
              ·
                refine ⟨13704789235671771910321729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18273052314229029213762305 13704789235671771910321729)
                ·
                  refine ⟨10278591926753828932741297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13704789235671771910321729 10278591926753828932741297)
                  ·
                    refine ⟨7708943945065371699555973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10278591926753828932741297 7708943945065371699555973)
                    ·
                      refine ⟨1445426989699757193666745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7708943945065371699555973 1445426989699757193666745)
                      ·
                        rfl

theorem cell23_2814959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 2, 2, 2, 4].length) (baseStart_2814959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2814959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2814959 prefixEnd_2814959 := by exact prefixLift 2814959
  have htrace : WordTrace (prefixWord ++ tailWord_2814959) baseStart_2814959 baseEnd_2814959 := by
    simpa [prefixWord, tailWord_2814959, baseEnd_2814959] using wordTrace_append hprefix tailTrace_2814959
  have hstable : (prefixWord ++ tailWord_2814959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2814959).length < 2 ^ (prefixWord ++ tailWord_2814959).sum := by decide
  have hdescent : baseEnd_2814959 < baseStart_2814959 := by decide
  rcases family_descends (prefixWord ++ tailWord_2814959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2814969 : List Nat := [1, 2, 1, 3, 1, 3, 4, 1, 7]
def baseStart_2814969 : Nat := 118140960795 + 2814969 * 2 ^ 59
def prefixEnd_2814969 : Nat := 4983230072969 + 3 ^ 40 * 2814969 * 2
def baseEnd_2814969 : Nat := 160603569389589128282411

theorem tailTrace_2814969 : CollatzResearch.WordTrace tailWord_2814969 prefixEnd_2814969 160603569389589128282411 := by
  unfold tailWord_2814969
  simp only [CollatzResearch.WordTrace]
  refine ⟨102670354138855546275175961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68446902759237030850117307 102670354138855546275175961)
  ·
    refine ⟨77002765604141659706381971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102670354138855546275175961 77002765604141659706381971)
    ·
      refine ⟨115504148406212489559572957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77002765604141659706381971 115504148406212489559572957)
      ·
        refine ⟨43314055652329683584839859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 115504148406212489559572957 43314055652329683584839859)
        ·
          refine ⟨64971083478494525377259789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43314055652329683584839859 64971083478494525377259789)
          ·
            refine ⟨24364156304435447016472421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64971083478494525377259789 24364156304435447016472421)
            ·
              refine ⟨4568279307081646315588579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24364156304435447016472421 4568279307081646315588579)
              ·
                refine ⟨6852418960622469473382869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4568279307081646315588579 6852418960622469473382869)
                ·
                  refine ⟨160603569389589128282411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6852418960622469473382869 160603569389589128282411)
                  ·
                    rfl

theorem cell23_2814969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 4, 1, 7].length) (baseStart_2814969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2814969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2814969 prefixEnd_2814969 := by exact prefixLift 2814969
  have htrace : WordTrace (prefixWord ++ tailWord_2814969) baseStart_2814969 baseEnd_2814969 := by
    simpa [prefixWord, tailWord_2814969, baseEnd_2814969] using wordTrace_append hprefix tailTrace_2814969
  have hstable : (prefixWord ++ tailWord_2814969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2814969).length < 2 ^ (prefixWord ++ tailWord_2814969).sum := by decide
  have hdescent : baseEnd_2814969 < baseStart_2814969 := by decide
  rcases family_descends (prefixWord ++ tailWord_2814969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2815053 : List Nat := [1, 6, 1, 1, 1, 2, 1, 3, 2, 1, 4]
def baseStart_2815053 : Nat := 118140960795 + 2815053 * 2 ^ 59
def prefixEnd_2815053 : Nat := 4983230072969 + 3 ^ 40 * 2815053 * 2
def baseEnd_2815053 : Nat := 1445475256881279825891313

theorem tailTrace_2815053 : CollatzResearch.WordTrace tailWord_2815053 prefixEnd_2815053 1445475256881279825891313 := by
  unfold tailWord_2815053
  simp only [CollatzResearch.WordTrace]
  refine ⟨102673417870551228621233813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68448945247034152414155875 102673417870551228621233813)
  ·
    refine ⟨4812816462682088841620335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 102673417870551228621233813 4812816462682088841620335)
    ·
      refine ⟨7219224694023133262430503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4812816462682088841620335 7219224694023133262430503)
      ·
        refine ⟨10828837041034699893645755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7219224694023133262430503 10828837041034699893645755)
        ·
          refine ⟨16243255561552049840468633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10828837041034699893645755 16243255561552049840468633)
          ·
            refine ⟨12182441671164037380351475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16243255561552049840468633 12182441671164037380351475)
            ·
              refine ⟨18273662506746056070527213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12182441671164037380351475 18273662506746056070527213)
              ·
                refine ⟨6852623440029771026447705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18273662506746056070527213 6852623440029771026447705)
                ·
                  refine ⟨5139467580022328269835779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6852623440029771026447705 5139467580022328269835779)
                  ·
                    refine ⟨7709201370033492404753669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5139467580022328269835779 7709201370033492404753669)
                    ·
                      refine ⟨1445475256881279825891313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7709201370033492404753669 1445475256881279825891313)
                      ·
                        rfl

theorem cell23_2815053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 3, 2, 1, 4].length) (baseStart_2815053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2815053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2815053 prefixEnd_2815053 := by exact prefixLift 2815053
  have htrace : WordTrace (prefixWord ++ tailWord_2815053) baseStart_2815053 baseEnd_2815053 := by
    simpa [prefixWord, tailWord_2815053, baseEnd_2815053] using wordTrace_append hprefix tailTrace_2815053
  have hstable : (prefixWord ++ tailWord_2815053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2815053).length < 2 ^ (prefixWord ++ tailWord_2815053).sum := by decide
  have hdescent : baseEnd_2815053 < baseStart_2815053 := by decide
  rcases family_descends (prefixWord ++ tailWord_2815053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2815063 : List Nat := [1, 1, 3, 2, 2, 1, 1, 7, 1, 4]
def baseStart_2815063 : Nat := 118140960795 + 2815063 * 2 ^ 59
def prefixEnd_2815063 : Nat := 4983230072969 + 3 ^ 40 * 2815063 * 2
def baseEnd_2815063 : Nat := 481826797229274928922089

theorem tailTrace_2815063 : CollatzResearch.WordTrace tailWord_2815063 prefixEnd_2815063 481826797229274928922089 := by
  unfold tailWord_2815063
  simp only [CollatzResearch.WordTrace]
  refine ⟨102673782600515000329097843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68449188400343333552731895 102673782600515000329097843)
  ·
    refine ⟨154010673900772500493646765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102673782600515000329097843 154010673900772500493646765)
    ·
      refine ⟨57754002712789687685117537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 154010673900772500493646765 57754002712789687685117537)
      ·
        refine ⟨43315502034592265763838153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57754002712789687685117537 43315502034592265763838153)
        ·
          refine ⟨32486626525944199322878615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43315502034592265763838153 32486626525944199322878615)
          ·
            refine ⟨48729939788916298984317923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32486626525944199322878615 48729939788916298984317923)
            ·
              refine ⟨73094909683374448476476885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48729939788916298984317923 73094909683374448476476885)
              ·
                refine ⟨1713161945704088636167427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 73094909683374448476476885 1713161945704088636167427)
                ·
                  refine ⟨2569742918556132954251141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1713161945704088636167427 2569742918556132954251141)
                  ·
                    refine ⟨481826797229274928922089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2569742918556132954251141 481826797229274928922089)
                    ·
                      rfl

theorem cell23_2815063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 7, 1, 4].length) (baseStart_2815063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2815063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2815063 prefixEnd_2815063 := by exact prefixLift 2815063
  have htrace : WordTrace (prefixWord ++ tailWord_2815063) baseStart_2815063 baseEnd_2815063 := by
    simpa [prefixWord, tailWord_2815063, baseEnd_2815063] using wordTrace_append hprefix tailTrace_2815063
  have hstable : (prefixWord ++ tailWord_2815063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2815063).length < 2 ^ (prefixWord ++ tailWord_2815063).sum := by decide
  have hdescent : baseEnd_2815063 < baseStart_2815063 := by decide
  rcases family_descends (prefixWord ++ tailWord_2815063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2815113 : List Nat := [1, 2, 1, 1, 4, 4, 1, 1, 1, 5, 2]
def baseStart_2815113 : Nat := 118140960795 + 2815113 * 2 ^ 59
def prefixEnd_2815113 : Nat := 4983230072969 + 3 ^ 40 * 2815113 * 2
def baseEnd_2815113 : Nat := 1445506065720549591141037

theorem tailTrace_2815113 : CollatzResearch.WordTrace tailWord_2815113 prefixEnd_2815113 1445506065720549591141037 := by
  unfold tailWord_2815113
  simp only [CollatzResearch.WordTrace]
  refine ⟨102675606250333858868417993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68450404166889239245611995 102675606250333858868417993)
  ·
    refine ⟨77006704687750394151313495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102675606250333858868417993 77006704687750394151313495)
    ·
      refine ⟨115510057031625591226970243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77006704687750394151313495 115510057031625591226970243)
      ·
        refine ⟨173265085547438386840455365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115510057031625591226970243 173265085547438386840455365)
        ·
          refine ⟨32487203540144697532585381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 173265085547438386840455365 32487203540144697532585381)
          ·
            refine ⟨6091350663777130787359759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32487203540144697532585381 6091350663777130787359759)
            ·
              refine ⟨9137025995665696181039639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6091350663777130787359759 9137025995665696181039639)
              ·
                refine ⟨13705538993498544271559459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9137025995665696181039639 13705538993498544271559459)
                ·
                  refine ⟨20558308490247816407339189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13705538993498544271559459 20558308490247816407339189)
                  ·
                    refine ⟨1927341420960732788188049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 20558308490247816407339189 1927341420960732788188049)
                    ·
                      refine ⟨1445506065720549591141037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1927341420960732788188049 1445506065720549591141037)
                      ·
                        rfl

theorem cell23_2815113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 1, 1, 1, 5, 2].length) (baseStart_2815113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2815113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2815113 prefixEnd_2815113 := by exact prefixLift 2815113
  have htrace : WordTrace (prefixWord ++ tailWord_2815113) baseStart_2815113 baseEnd_2815113 := by
    simpa [prefixWord, tailWord_2815113, baseEnd_2815113] using wordTrace_append hprefix tailTrace_2815113
  have hstable : (prefixWord ++ tailWord_2815113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2815113).length < 2 ^ (prefixWord ++ tailWord_2815113).sum := by decide
  have hdescent : baseEnd_2815113 < baseStart_2815113 := by decide
  rcases family_descends (prefixWord ++ tailWord_2815113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2815119 : List Nat := [1, 1, 2, 1, 1, 1, 1, 2, 7, 6]
def baseStart_2815119 : Nat := 118140960795 + 2815119 * 2 ^ 59
def prefixEnd_2815119 : Nat := 4983230072969 + 3 ^ 40 * 2815119 * 2
def baseEnd_2815119 : Nat := 481836382201492189222003

theorem tailTrace_2815119 : CollatzResearch.WordTrace tailWord_2815119 prefixEnd_2815119 481836382201492189222003 := by
  unfold tailWord_2815119
  simp only [CollatzResearch.WordTrace]
  refine ⟨102675825088312121893136411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68450550058874747928757607 102675825088312121893136411)
  ·
    refine ⟨154013737632468182839704617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102675825088312121893136411 154013737632468182839704617)
    ·
      refine ⟨115510303224351137129778463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154013737632468182839704617 115510303224351137129778463)
      ·
        refine ⟨173265454836526705694667695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115510303224351137129778463 173265454836526705694667695)
        ·
          refine ⟨259898182254790058542001543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173265454836526705694667695 259898182254790058542001543)
          ·
            refine ⟨389847273382185087813002315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 259898182254790058542001543 389847273382185087813002315)
            ·
              refine ⟨584770910073277631719503473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 389847273382185087813002315 584770910073277631719503473)
              ·
                refine ⟨438578182554958223789627605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 584770910073277631719503473 438578182554958223789627605)
                ·
                  refine ⟨10279176153631833370069397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 438578182554958223789627605 10279176153631833370069397)
                  ·
                    refine ⟨481836382201492189222003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10279176153631833370069397 481836382201492189222003)
                    ·
                      rfl

theorem cell23_2815119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 7, 6].length) (baseStart_2815119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2815119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2815119 prefixEnd_2815119 := by exact prefixLift 2815119
  have htrace : WordTrace (prefixWord ++ tailWord_2815119) baseStart_2815119 baseEnd_2815119 := by
    simpa [prefixWord, tailWord_2815119, baseEnd_2815119] using wordTrace_append hprefix tailTrace_2815119
  have hstable : (prefixWord ++ tailWord_2815119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2815119).length < 2 ^ (prefixWord ++ tailWord_2815119).sum := by decide
  have hdescent : baseEnd_2815119 < baseStart_2815119 := by decide
  rcases family_descends (prefixWord ++ tailWord_2815119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2815123 : List Nat := [1, 1, 1, 2, 1, 2, 8, 1, 1, 5]
def baseStart_2815123 : Nat := 118140960795 + 2815123 * 2 ^ 59
def prefixEnd_2815123 : Nat := 4983230072969 + 3 ^ 40 * 2815123 * 2
def baseEnd_2815123 : Nat := 481837066842364850671997

theorem tailTrace_2815123 : CollatzResearch.WordTrace tailWord_2815123 prefixEnd_2815123 481837066842364850671997 := by
  unfold tailWord_2815123
  simp only [CollatzResearch.WordTrace]
  refine ⟨102675970980297630576282023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68450647320198420384188015 102675970980297630576282023)
  ·
    refine ⟨154013956470446445864423035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102675970980297630576282023 154013956470446445864423035)
    ·
      refine ⟨231020934705669668796634553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154013956470446445864423035 231020934705669668796634553)
      ·
        refine ⟨173265701029252251597475915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 231020934705669668796634553 173265701029252251597475915)
        ·
          refine ⟨259898551543878377396213873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173265701029252251597475915 259898551543878377396213873)
          ·
            refine ⟨194923913657908783047160405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 259898551543878377396213873 194923913657908783047160405)
            ·
              refine ⟨2284264613178618551333911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 194923913657908783047160405 2284264613178618551333911)
              ·
                refine ⟨3426396919767927827000867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2284264613178618551333911 3426396919767927827000867)
                ·
                  refine ⟨5139595379651891740501301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3426396919767927827000867 5139595379651891740501301)
                  ·
                    refine ⟨481837066842364850671997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5139595379651891740501301 481837066842364850671997)
                    ·
                      rfl

theorem cell23_2815123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 8, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 8, 1, 1, 5].length) (baseStart_2815123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2815123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2815123 prefixEnd_2815123 := by exact prefixLift 2815123
  have htrace : WordTrace (prefixWord ++ tailWord_2815123) baseStart_2815123 baseEnd_2815123 := by
    simpa [prefixWord, tailWord_2815123, baseEnd_2815123] using wordTrace_append hprefix tailTrace_2815123
  have hstable : (prefixWord ++ tailWord_2815123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2815123).length < 2 ^ (prefixWord ++ tailWord_2815123).sum := by decide
  have hdescent : baseEnd_2815123 < baseStart_2815123 := by decide
  rcases family_descends (prefixWord ++ tailWord_2815123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2815153 : List Nat := [1, 2, 2, 5, 1, 1, 3, 1, 1, 6]
def baseStart_2815153 : Nat := 118140960795 + 2815153 * 2 ^ 59
def prefixEnd_2815153 : Nat := 4983230072969 + 3 ^ 40 * 2815153 * 2
def baseEnd_2815153 : Nat := 481842201648909811546951

theorem tailTrace_2815153 : CollatzResearch.WordTrace tailWord_2815153 prefixEnd_2815153 481842201648909811546951 := by
  unfold tailWord_2815153
  simp only [CollatzResearch.WordTrace]
  refine ⟨102677065170188945699874113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68451376780125963799916075 102677065170188945699874113)
  ·
    refine ⟨77007798877641709274905585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102677065170188945699874113 77007798877641709274905585)
    ·
      refine ⟨57755849158231281956179189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77007798877641709274905585 57755849158231281956179189)
      ·
        refine ⟨5414610858584182683391799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 57755849158231281956179189 5414610858584182683391799)
        ·
          refine ⟨8121916287876274025087699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5414610858584182683391799 8121916287876274025087699)
          ·
            refine ⟨12182874431814411037631549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8121916287876274025087699 12182874431814411037631549)
            ·
              refine ⟨4568577911930404139111831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12182874431814411037631549 4568577911930404139111831)
              ·
                refine ⟨6852866867895606208667747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4568577911930404139111831 6852866867895606208667747)
                ·
                  refine ⟨10279300301843409313001621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6852866867895606208667747 10279300301843409313001621)
                  ·
                    refine ⟨481842201648909811546951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10279300301843409313001621 481842201648909811546951)
                    ·
                      rfl

theorem cell23_2815153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 3, 1, 1, 6].length) (baseStart_2815153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2815153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2815153 prefixEnd_2815153 := by exact prefixLift 2815153
  have htrace : WordTrace (prefixWord ++ tailWord_2815153) baseStart_2815153 baseEnd_2815153 := by
    simpa [prefixWord, tailWord_2815153, baseEnd_2815153] using wordTrace_append hprefix tailTrace_2815153
  have hstable : (prefixWord ++ tailWord_2815153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2815153).length < 2 ^ (prefixWord ++ tailWord_2815153).sum := by decide
  have hdescent : baseEnd_2815153 < baseStart_2815153 := by decide
  rcases family_descends (prefixWord ++ tailWord_2815153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2815237 : List Nat := [1, 3, 1, 1, 2, 1, 7, 1, 1, 3, 2]
def baseStart_2815237 : Nat := 118140960795 + 2815237 * 2 ^ 59
def prefixEnd_2815237 : Nat := 4983230072969 + 3 ^ 40 * 2815237 * 2
def baseEnd_2815237 : Nat := 1445569737321707105990467

theorem tailTrace_2815237 : CollatzResearch.WordTrace tailWord_2815237 prefixEnd_2815237 1445569737321707105990467 := by
  unfold tailWord_2815237
  simp only [CollatzResearch.WordTrace]
  refine ⟨102680128901884628045931965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68453419267923085363954643 102680128901884628045931965)
  ·
    refine ⟨38505048338206735517224487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102680128901884628045931965 38505048338206735517224487)
    ·
      refine ⟨57757572507310103275836731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38505048338206735517224487 57757572507310103275836731)
      ·
        refine ⟨86636358760965154913755097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57757572507310103275836731 86636358760965154913755097)
        ·
          refine ⟨64977269070723866185316323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86636358760965154913755097 64977269070723866185316323)
          ·
            refine ⟨97465903606085799277974485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64977269070723866185316323 97465903606085799277974485)
            ·
              refine ⟨2284357115767635920577527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 97465903606085799277974485 2284357115767635920577527)
              ·
                refine ⟨3426535673651453880866291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2284357115767635920577527 3426535673651453880866291)
                ·
                  refine ⟨5139803510477180821299437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3426535673651453880866291 5139803510477180821299437)
                  ·
                    refine ⟨1927426316428942807987289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5139803510477180821299437 1927426316428942807987289)
                    ·
                      refine ⟨1445569737321707105990467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1927426316428942807987289 1445569737321707105990467)
                      ·
                        rfl

theorem cell23_2815237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 7, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 7, 1, 1, 3, 2].length) (baseStart_2815237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2815237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2815237 prefixEnd_2815237 := by exact prefixLift 2815237
  have htrace : WordTrace (prefixWord ++ tailWord_2815237) baseStart_2815237 baseEnd_2815237 := by
    simpa [prefixWord, tailWord_2815237, baseEnd_2815237] using wordTrace_append hprefix tailTrace_2815237
  have hstable : (prefixWord ++ tailWord_2815237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2815237).length < 2 ^ (prefixWord ++ tailWord_2815237).sum := by decide
  have hdescent : baseEnd_2815237 < baseStart_2815237 := by decide
  rcases family_descends (prefixWord ++ tailWord_2815237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2815267 : List Nat := [1, 1, 1, 4, 2, 3, 2, 3, 2, 2, 2]
def baseStart_2815267 : Nat := 118140960795 + 2815267 * 2 ^ 59
def prefixEnd_2815267 : Nat := 4983230072969 + 3 ^ 40 * 2815267 * 2
def baseEnd_2815267 : Nat := 1445585141741341988615329

theorem tailTrace_2815267 : CollatzResearch.WordTrace tailWord_2815267 prefixEnd_2815267 1445585141741341988615329 := by
  unfold tailWord_2815267
  simp only [CollatzResearch.WordTrace]
  refine ⟨102681223091775943169524055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68454148727850628779682703 102681223091775943169524055)
  ·
    refine ⟨154021834637663914754286083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102681223091775943169524055 154021834637663914754286083)
    ·
      refine ⟨231032751956495872131429125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154021834637663914754286083 231032751956495872131429125)
      ·
        refine ⟨43318640991842976024642961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 231032751956495872131429125 43318640991842976024642961)
        ·
          refine ⟨32488980743882232018482221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43318640991842976024642961 32488980743882232018482221)
          ·
            refine ⟨12183367778955837006930833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32488980743882232018482221 12183367778955837006930833)
            ·
              refine ⟨9137525834216877755198125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12183367778955837006930833 9137525834216877755198125)
              ·
                refine ⟨3426572187831329158199297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9137525834216877755198125 3426572187831329158199297)
                ·
                  refine ⟨2569929140873496868649473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3426572187831329158199297 2569929140873496868649473)
                  ·
                    refine ⟨1927446855655122651487105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2569929140873496868649473 1927446855655122651487105)
                    ·
                      refine ⟨1445585141741341988615329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1927446855655122651487105 1445585141741341988615329)
                      ·
                        rfl

theorem cell23_2815267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 2, 3, 2, 2, 2].length) (baseStart_2815267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2815267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2815267 prefixEnd_2815267 := by exact prefixLift 2815267
  have htrace : WordTrace (prefixWord ++ tailWord_2815267) baseStart_2815267 baseEnd_2815267 := by
    simpa [prefixWord, tailWord_2815267, baseEnd_2815267] using wordTrace_append hprefix tailTrace_2815267
  have hstable : (prefixWord ++ tailWord_2815267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2815267).length < 2 ^ (prefixWord ++ tailWord_2815267).sum := by decide
  have hdescent : baseEnd_2815267 < baseStart_2815267 := by decide
  rcases family_descends (prefixWord ++ tailWord_2815267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2815290 : List Nat := [3, 1, 1, 1, 4, 1, 4, 3, 5]
def baseStart_2815290 : Nat := 118140960795 + 2815290 * 2 ^ 59
def prefixEnd_2815290 : Nat := 4983230072969 + 3 ^ 40 * 2815290 * 2
def baseEnd_2815290 : Nat := 160621883532932822069747

theorem tailTrace_2815290 : CollatzResearch.WordTrace tailWord_2815290 prefixEnd_2815290 160621883532932822069747 := by
  unfold tailWord_2815290
  simp only [CollatzResearch.WordTrace]
  refine ⟨25670515492673154524402831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68454707980461745398407549 25670515492673154524402831)
  ·
    refine ⟨38505773239009731786604247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25670515492673154524402831 38505773239009731786604247)
    ·
      refine ⟨57758659858514597679906371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38505773239009731786604247 57758659858514597679906371)
      ·
        refine ⟨86637989787771896519859557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57758659858514597679906371 86637989787771896519859557)
        ·
          refine ⟨16244623085207230597473667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 86637989787771896519859557 16244623085207230597473667)
          ·
            refine ⟨24366934627810845896210501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16244623085207230597473667 24366934627810845896210501)
            ·
              refine ⟨4568800242714533605539469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24366934627810845896210501 4568800242714533605539469)
              ·
                refine ⟨1713300091017950102077301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4568800242714533605539469 1713300091017950102077301)
                ·
                  refine ⟨160621883532932822069747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1713300091017950102077301 160621883532932822069747)
                  ·
                    rfl

theorem cell23_2815290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 4, 3, 5].length) (baseStart_2815290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2815290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2815290 prefixEnd_2815290 := by exact prefixLift 2815290
  have htrace : WordTrace (prefixWord ++ tailWord_2815290) baseStart_2815290 baseEnd_2815290 := by
    simpa [prefixWord, tailWord_2815290, baseEnd_2815290] using wordTrace_append hprefix tailTrace_2815290
  have hstable : (prefixWord ++ tailWord_2815290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2815290).length < 2 ^ (prefixWord ++ tailWord_2815290).sum := by decide
  have hdescent : baseEnd_2815290 < baseStart_2815290 := by decide
  rcases family_descends (prefixWord ++ tailWord_2815290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2815343 : List Nat := [1, 1, 2, 1, 3, 1, 3, 3, 1, 4, 3]
def baseStart_2815343 : Nat := 118140960795 + 2815343 * 2 ^ 59
def prefixEnd_2815343 : Nat := 4983230072969 + 3 ^ 40 * 2815343 * 2
def baseEnd_2815343 : Nat := 1445624166271083691264979

theorem tailTrace_2815343 : CollatzResearch.WordTrace tailWord_2815343 prefixEnd_2815343 1445624166271083691264979 := by
  unfold tailWord_2815343
  simp only [CollatzResearch.WordTrace]
  refine ⟨102683995039500608149290683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68455996693000405432860455 102683995039500608149290683)
  ·
    refine ⟨154025992559250912223936025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102683995039500608149290683 154025992559250912223936025)
    ·
      refine ⟨115519494419438184167952019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154025992559250912223936025 115519494419438184167952019)
      ·
        refine ⟨173279241629157276251928029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115519494419438184167952019 173279241629157276251928029)
        ·
          refine ⟨64979715610933978594473011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 173279241629157276251928029 64979715610933978594473011)
          ·
            refine ⟨97469573416400967891709517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64979715610933978594473011 97469573416400967891709517)
            ·
              refine ⟨36551090031150362959391069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 97469573416400967891709517 36551090031150362959391069)
              ·
                refine ⟨13706658761681386109771651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36551090031150362959391069 13706658761681386109771651)
                ·
                  refine ⟨20559988142522079164657477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13706658761681386109771651 20559988142522079164657477)
                  ·
                    refine ⟨3854997776722889843373277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20559988142522079164657477 3854997776722889843373277)
                    ·
                      refine ⟨1445624166271083691264979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3854997776722889843373277 1445624166271083691264979)
                      ·
                        rfl

theorem cell23_2815343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 3, 1, 4, 3].length) (baseStart_2815343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2815343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2815343 prefixEnd_2815343 := by exact prefixLift 2815343
  have htrace : WordTrace (prefixWord ++ tailWord_2815343) baseStart_2815343 baseEnd_2815343 := by
    simpa [prefixWord, tailWord_2815343, baseEnd_2815343] using wordTrace_append hprefix tailTrace_2815343
  have hstable : (prefixWord ++ tailWord_2815343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2815343).length < 2 ^ (prefixWord ++ tailWord_2815343).sum := by decide
  have hdescent : baseEnd_2815343 < baseStart_2815343 := by decide
  rcases family_descends (prefixWord ++ tailWord_2815343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2815363 : List Nat := [1, 1, 1, 3, 5, 1, 2, 1, 8]
def baseStart_2815363 : Nat := 118140960795 + 2815363 * 2 ^ 59
def prefixEnd_2815363 : Nat := 4983230072969 + 3 ^ 40 * 2815363 * 2
def baseEnd_2815363 : Nat := 160626048431574845890543

theorem tailTrace_2815363 : CollatzResearch.WordTrace tailWord_2815363 prefixEnd_2815363 160626048431574845890543 := by
  unfold tailWord_2815363
  simp only [CollatzResearch.WordTrace]
  refine ⟨102684724499428151565018743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68456482999618767710012495 102684724499428151565018743)
  ·
    refine ⟨154027086749142227347528115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102684724499428151565018743 154027086749142227347528115)
    ·
      refine ⟨231040630123713341021292173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154027086749142227347528115 231040630123713341021292173)
      ·
        refine ⟨86640236296392502882984565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 231040630123713341021292173 86640236296392502882984565)
        ·
          refine ⟨8122522152786797145279803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 86640236296392502882984565 8122522152786797145279803)
          ·
            refine ⟨12183783229180195717919705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8122522152786797145279803 12183783229180195717919705)
            ·
              refine ⟨9137837421885146788439779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12183783229180195717919705 9137837421885146788439779)
              ·
                refine ⟨13706756132827720182659669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9137837421885146788439779 13706756132827720182659669)
                ·
                  refine ⟨160626048431574845890543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 13706756132827720182659669 160626048431574845890543)
                  ·
                    rfl

theorem cell23_2815363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 2, 1, 8].length) (baseStart_2815363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2815363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2815363 prefixEnd_2815363 := by exact prefixLift 2815363
  have htrace : WordTrace (prefixWord ++ tailWord_2815363) baseStart_2815363 baseEnd_2815363 := by
    simpa [prefixWord, tailWord_2815363, baseEnd_2815363] using wordTrace_append hprefix tailTrace_2815363
  have hstable : (prefixWord ++ tailWord_2815363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2815363).length < 2 ^ (prefixWord ++ tailWord_2815363).sum := by decide
  have hdescent : baseEnd_2815363 < baseStart_2815363 := by decide
  rcases family_descends (prefixWord ++ tailWord_2815363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2815367 : List Nat := [1, 1, 4, 2, 2, 4, 1, 1, 3, 4]
def baseStart_2815367 : Nat := 118140960795 + 2815367 * 2 ^ 59
def prefixEnd_2815367 : Nat := 4983230072969 + 3 ^ 40 * 2815367 * 2
def baseEnd_2815367 : Nat := 481878829935597199121623

theorem tailTrace_2815367 : CollatzResearch.WordTrace tailWord_2815367 prefixEnd_2815367 481878829935597199121623 := by
  unfold tailWord_2815367
  simp only [CollatzResearch.WordTrace]
  refine ⟨102684870391413660248164355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68456580260942440165442903 102684870391413660248164355)
  ·
    refine ⟨154027305587120490372246533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102684870391413660248164355 154027305587120490372246533)
    ·
      refine ⟨28880119797585091944796225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 154027305587120490372246533 28880119797585091944796225)
      ·
        refine ⟨21660089848188818958597169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28880119797585091944796225 21660089848188818958597169)
        ·
          refine ⟨16245067386141614218947877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21660089848188818958597169 16245067386141614218947877)
          ·
            refine ⟨3045950134901552666052727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16245067386141614218947877 3045950134901552666052727)
            ·
              refine ⟨4568925202352328999079091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3045950134901552666052727 4568925202352328999079091)
              ·
                refine ⟨6853387803528493498618637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4568925202352328999079091 6853387803528493498618637)
                ·
                  refine ⟨2570020426323185061981989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6853387803528493498618637 2570020426323185061981989)
                  ·
                    refine ⟨481878829935597199121623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2570020426323185061981989 481878829935597199121623)
                    ·
                      rfl

theorem cell23_2815367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 1, 1, 3, 4].length) (baseStart_2815367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2815367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2815367 prefixEnd_2815367 := by exact prefixLift 2815367
  have htrace : WordTrace (prefixWord ++ tailWord_2815367) baseStart_2815367 baseEnd_2815367 := by
    simpa [prefixWord, tailWord_2815367, baseEnd_2815367] using wordTrace_append hprefix tailTrace_2815367
  have hstable : (prefixWord ++ tailWord_2815367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2815367).length < 2 ^ (prefixWord ++ tailWord_2815367).sum := by decide
  have hdescent : baseEnd_2815367 < baseStart_2815367 := by decide
  rcases family_descends (prefixWord ++ tailWord_2815367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2815433 : List Nat := [1, 2, 1, 1, 2, 1, 3, 3, 3, 1, 5]
def baseStart_2815433 : Nat := 118140960795 + 2815433 * 2 ^ 59
def prefixEnd_2815433 : Nat := 4983230072969 + 3 ^ 40 * 2815433 * 2
def baseEnd_2815433 : Nat := 1445670379529988339139565

theorem tailTrace_2815433 : CollatzResearch.WordTrace tailWord_2815433 prefixEnd_2815433 1445670379529988339139565 := by
  unfold tailWord_2815433
  simp only [CollatzResearch.WordTrace]
  refine ⟨102687277609174553520066953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68458185072783035680044635 102687277609174553520066953)
  ·
    refine ⟨77015458206880915140050215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102687277609174553520066953 77015458206880915140050215)
    ·
      refine ⟨115523187310321372710075323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77015458206880915140050215 115523187310321372710075323)
      ·
        refine ⟨173284780965482059065112985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115523187310321372710075323 173284780965482059065112985)
        ·
          refine ⟨129963585724111544298834739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 173284780965482059065112985 129963585724111544298834739)
          ·
            refine ⟨194945378586167316448252109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129963585724111544298834739 194945378586167316448252109)
            ·
              refine ⟨73104516969812743668094541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 194945378586167316448252109 73104516969812743668094541)
              ·
                refine ⟨27414193863679778875535453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 73104516969812743668094541 27414193863679778875535453)
                ·
                  refine ⟨10280322698879917078325795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27414193863679778875535453 10280322698879917078325795)
                  ·
                    refine ⟨15420484048319875617488693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10280322698879917078325795 15420484048319875617488693)
                    ·
                      refine ⟨1445670379529988339139565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15420484048319875617488693 1445670379529988339139565)
                      ·
                        rfl

theorem cell23_2815433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 3, 3, 1, 5].length) (baseStart_2815433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2815433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2815433 prefixEnd_2815433 := by exact prefixLift 2815433
  have htrace : WordTrace (prefixWord ++ tailWord_2815433) baseStart_2815433 baseEnd_2815433 := by
    simpa [prefixWord, tailWord_2815433, baseEnd_2815433] using wordTrace_append hprefix tailTrace_2815433
  have hstable : (prefixWord ++ tailWord_2815433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2815433).length < 2 ^ (prefixWord ++ tailWord_2815433).sum := by decide
  have hdescent : baseEnd_2815433 < baseStart_2815433 := by decide
  rcases family_descends (prefixWord ++ tailWord_2815433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2815474 : List Nat := [3, 2, 1, 4, 1, 1, 3, 2, 2, 4]
def baseStart_2815474 : Nat := 118140960795 + 2815474 * 2 ^ 59
def prefixEnd_2815474 : Nat := 4983230072969 + 3 ^ 40 * 2815474 * 2
def baseEnd_2815474 : Nat := 481897144078940892908959

theorem tailTrace_2815474 : CollatzResearch.WordTrace tailWord_2815474 prefixEnd_2815474 481897144078940892908959 := by
  unfold tailWord_2815474
  simp only [CollatzResearch.WordTrace]
  refine ⟨25672193250506504380577369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68459182001350678348206317 25672193250506504380577369)
  ·
    refine ⟨19254144937879878285433027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25672193250506504380577369 19254144937879878285433027)
    ·
      refine ⟨28881217406819817428149541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19254144937879878285433027 28881217406819817428149541)
      ·
        refine ⟨5415228263778715767778039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28881217406819817428149541 5415228263778715767778039)
        ·
          refine ⟨8122842395668073651667059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5415228263778715767778039 8122842395668073651667059)
          ·
            refine ⟨12184263593502110477500589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8122842395668073651667059 12184263593502110477500589)
            ·
              refine ⟨4569098847563291429062721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12184263593502110477500589 4569098847563291429062721)
              ·
                refine ⟨3426824135672468571797041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4569098847563291429062721 3426824135672468571797041)
                ·
                  refine ⟨2570118101754351428847781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3426824135672468571797041 2570118101754351428847781)
                  ·
                    refine ⟨481897144078940892908959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2570118101754351428847781 481897144078940892908959)
                    ·
                      rfl

theorem cell23_2815474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 3, 2, 2, 4].length) (baseStart_2815474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2815474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2815474 prefixEnd_2815474 := by exact prefixLift 2815474
  have htrace : WordTrace (prefixWord ++ tailWord_2815474) baseStart_2815474 baseEnd_2815474 := by
    simpa [prefixWord, tailWord_2815474, baseEnd_2815474] using wordTrace_append hprefix tailTrace_2815474
  have hstable : (prefixWord ++ tailWord_2815474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2815474).length < 2 ^ (prefixWord ++ tailWord_2815474).sum := by decide
  have hdescent : baseEnd_2815474 < baseStart_2815474 := by decide
  rcases family_descends (prefixWord ++ tailWord_2815474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2815518 : List Nat := [4, 3, 3, 1, 1, 1, 2, 1, 1, 1, 5]
def baseStart_2815518 : Nat := 118140960795 + 2815518 * 2 ^ 59
def prefixEnd_2815518 : Nat := 4983230072969 + 3 ^ 40 * 2815518 * 2
def baseEnd_2815518 : Nat := 1445714025385620506576675

theorem tailTrace_2815518 : CollatzResearch.WordTrace tailWord_2815518 prefixEnd_2815518 1445714025385620506576675 := by
  unfold tailWord_2815518
  simp only [CollatzResearch.WordTrace]
  refine ⟨12836297226733326629613901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68460251875911075357940805 12836297226733326629613901)
  ·
    refine ⟨4813611460024997486105213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12836297226733326629613901 4813611460024997486105213)
    ·
      refine ⟨1805104297509374057289455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4813611460024997486105213 1805104297509374057289455)
      ·
        refine ⟨2707656446264061085934183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1805104297509374057289455 2707656446264061085934183)
        ·
          refine ⟨4061484669396091628901275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2707656446264061085934183 4061484669396091628901275)
          ·
            refine ⟨6092227004094137443351913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4061484669396091628901275 6092227004094137443351913)
            ·
              refine ⟨4569170253070603082513935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6092227004094137443351913 4569170253070603082513935)
              ·
                refine ⟨6853755379605904623770903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4569170253070603082513935 6853755379605904623770903)
                ·
                  refine ⟨10280633069408856935656355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6853755379605904623770903 10280633069408856935656355)
                  ·
                    refine ⟨15420949604113285403484533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10280633069408856935656355 15420949604113285403484533)
                    ·
                      refine ⟨1445714025385620506576675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15420949604113285403484533 1445714025385620506576675)
                      ·
                        rfl

theorem cell23_2815518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 2, 1, 1, 1, 5].length) (baseStart_2815518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2815518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2815518 prefixEnd_2815518 := by exact prefixLift 2815518
  have htrace : WordTrace (prefixWord ++ tailWord_2815518) baseStart_2815518 baseEnd_2815518 := by
    simpa [prefixWord, tailWord_2815518, baseEnd_2815518] using wordTrace_append hprefix tailTrace_2815518
  have hstable : (prefixWord ++ tailWord_2815518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2815518).length < 2 ^ (prefixWord ++ tailWord_2815518).sum := by decide
  have hdescent : baseEnd_2815518 < baseStart_2815518 := by decide
  rcases family_descends (prefixWord ++ tailWord_2815518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2815548 : List Nat := [2, 2, 2, 2, 4, 2, 2, 1, 2, 1, 3]
def baseStart_2815548 : Nat := 118140960795 + 2815548 * 2 ^ 59
def prefixEnd_2815548 : Nat := 4983230072969 + 3 ^ 40 * 2815548 * 2
def baseEnd_2815548 : Nat := 1445729429805255389201537

theorem tailTrace_2815548 : CollatzResearch.WordTrace tailWord_2815548 prefixEnd_2815548 1445729429805255389201537 := by
  unfold tailWord_2815548
  simp only [CollatzResearch.WordTrace]
  refine ⟨51345736001878964080251649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68460981335838618773668865 51345736001878964080251649)
  ·
    refine ⟨38509302001409223060188737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51345736001878964080251649 38509302001409223060188737)
    ·
      refine ⟨28881976501056917295141553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38509302001409223060188737 28881976501056917295141553)
      ·
        refine ⟨21661482375792687971356165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28881976501056917295141553 21661482375792687971356165)
        ·
          refine ⟨4061527945461128994629281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21661482375792687971356165 4061527945461128994629281)
          ·
            refine ⟨3046145959095846745971961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4061527945461128994629281 3046145959095846745971961)
            ·
              refine ⟨2284609469321885059478971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3046145959095846745971961 2284609469321885059478971)
              ·
                refine ⟨3426914203982827589218457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2284609469321885059478971 3426914203982827589218457)
                ·
                  refine ⟨2570185652987120691913843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3426914203982827589218457 2570185652987120691913843)
                  ·
                    refine ⟨3855278479480681037870765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2570185652987120691913843 3855278479480681037870765)
                    ·
                      refine ⟨1445729429805255389201537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3855278479480681037870765 1445729429805255389201537)
                      ·
                        rfl

theorem cell23_2815548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 2, 1, 2, 1, 3].length) (baseStart_2815548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2815548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2815548 prefixEnd_2815548 := by exact prefixLift 2815548
  have htrace : WordTrace (prefixWord ++ tailWord_2815548) baseStart_2815548 baseEnd_2815548 := by
    simpa [prefixWord, tailWord_2815548, baseEnd_2815548] using wordTrace_append hprefix tailTrace_2815548
  have hstable : (prefixWord ++ tailWord_2815548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2815548).length < 2 ^ (prefixWord ++ tailWord_2815548).sum := by decide
  have hdescent : baseEnd_2815548 < baseStart_2815548 := by decide
  rcases family_descends (prefixWord ++ tailWord_2815548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2815558 : List Nat := [6, 1, 1, 1, 3, 1, 1, 1, 3, 3, 2]
def baseStart_2815558 : Nat := 118140960795 + 2815558 * 2 ^ 59
def prefixEnd_2815558 : Nat := 4983230072969 + 3 ^ 40 * 2815558 * 2
def baseEnd_2815558 : Nat := 1445734564611800350076491

theorem tailTrace_2815558 : CollatzResearch.WordTrace tailWord_2815558 prefixEnd_2815558 1445734564611800350076491 := by
  unfold tailWord_2815558
  simp only [CollatzResearch.WordTrace]
  refine ⟨3209119897928803120886479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 68461224489147799912244885 3209119897928803120886479)
  ·
    refine ⟨4813679846893204681329719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3209119897928803120886479 4813679846893204681329719)
    ·
      refine ⟨7220519770339807021994579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4813679846893204681329719 7220519770339807021994579)
      ·
        refine ⟨10830779655509710532991869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7220519770339807021994579 10830779655509710532991869)
        ·
          refine ⟨4061542370816141449871951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10830779655509710532991869 4061542370816141449871951)
          ·
            refine ⟨6092313556224212174807927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4061542370816141449871951 6092313556224212174807927)
            ·
              refine ⟨9138470334336318262211891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6092313556224212174807927 9138470334336318262211891)
              ·
                refine ⟨13707705501504477393317837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9138470334336318262211891 13707705501504477393317837)
                ·
                  refine ⟨5140389563064179022494189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13707705501504477393317837 5140389563064179022494189)
                  ·
                    refine ⟨1927646086149067133435321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5140389563064179022494189 1927646086149067133435321)
                    ·
                      refine ⟨1445734564611800350076491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1927646086149067133435321 1445734564611800350076491)
                      ·
                        rfl

theorem cell23_2815558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 1, 1, 3, 3, 2].length) (baseStart_2815558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2815558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2815558 prefixEnd_2815558 := by exact prefixLift 2815558
  have htrace : WordTrace (prefixWord ++ tailWord_2815558) baseStart_2815558 baseEnd_2815558 := by
    simpa [prefixWord, tailWord_2815558, baseEnd_2815558] using wordTrace_append hprefix tailTrace_2815558
  have hstable : (prefixWord ++ tailWord_2815558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2815558).length < 2 ^ (prefixWord ++ tailWord_2815558).sum := by decide
  have hdescent : baseEnd_2815558 < baseStart_2815558 := by decide
  rcases family_descends (prefixWord ++ tailWord_2815558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2815594 : List Nat := [3, 1, 3, 2, 1, 3, 1, 4, 5]
def baseStart_2815594 : Nat := 118140960795 + 2815594 * 2 ^ 59
def prefixEnd_2815594 : Nat := 4983230072969 + 3 ^ 40 * 2815594 * 2
def baseEnd_2815594 : Nat := 160639227768373578802925

theorem tailTrace_2815594 : CollatzResearch.WordTrace tailWord_2815594 prefixEnd_2815594 160639227768373578802925 := by
  unfold tailWord_2815594
  simp only [CollatzResearch.WordTrace]
  refine ⟨25673287440397819504169459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68462099841060852011118557 25673287440397819504169459)
  ·
    refine ⟨38509931160596729256254189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25673287440397819504169459 38509931160596729256254189)
    ·
      refine ⟨14441224185223773471095321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38509931160596729256254189 14441224185223773471095321)
      ·
        refine ⟨10830918138917830103321491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14441224185223773471095321 10830918138917830103321491)
        ·
          refine ⟨16246377208376745154982237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10830918138917830103321491 16246377208376745154982237)
          ·
            refine ⟨6092391453141279433118339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16246377208376745154982237 6092391453141279433118339)
            ·
              refine ⟨9138587179711919149677509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6092391453141279433118339 9138587179711919149677509)
              ·
                refine ⟨1713485096195984840564533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9138587179711919149677509 1713485096195984840564533)
                ·
                  refine ⟨160639227768373578802925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1713485096195984840564533 160639227768373578802925)
                  ·
                    rfl

theorem cell23_2815594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 1, 4, 5].length) (baseStart_2815594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2815594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2815594 prefixEnd_2815594 := by exact prefixLift 2815594
  have htrace : WordTrace (prefixWord ++ tailWord_2815594) baseStart_2815594 baseEnd_2815594 := by
    simpa [prefixWord, tailWord_2815594, baseEnd_2815594] using wordTrace_append hprefix tailTrace_2815594
  have hstable : (prefixWord ++ tailWord_2815594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2815594).length < 2 ^ (prefixWord ++ tailWord_2815594).sum := by decide
  have hdescent : baseEnd_2815594 < baseStart_2815594 := by decide
  rcases family_descends (prefixWord ++ tailWord_2815594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2815624 : List Nat := [2, 1, 3, 5, 1, 1, 1, 1, 1, 7]
def baseStart_2815624 : Nat := 118140960795 + 2815624 * 2 ^ 59
def prefixEnd_2815624 : Nat := 4983230072969 + 3 ^ 40 * 2815624 * 2
def baseEnd_2815624 : Nat := 481922818111665697283729

theorem tailTrace_2815624 : CollatzResearch.WordTrace tailWord_2815624 prefixEnd_2815624 481922818111665697283729 := by
  unfold tailWord_2815624
  simp only [CollatzResearch.WordTrace]
  refine ⟨51347121975741296570134963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68462829300988395426846617 51347121975741296570134963)
  ·
    refine ⟨77020682963611944855202445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51347121975741296570134963 77020682963611944855202445)
    ·
      refine ⟨28882756111354479320700917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77020682963611944855202445 28882756111354479320700917)
      ·
        refine ⟨2707758385439482436315711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 28882756111354479320700917 2707758385439482436315711)
        ·
          refine ⟨4061637578159223654473567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2707758385439482436315711 4061637578159223654473567)
          ·
            refine ⟨6092456367238835481710351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4061637578159223654473567 6092456367238835481710351)
            ·
              refine ⟨9138684550858253222565527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6092456367238835481710351 9138684550858253222565527)
              ·
                refine ⟨13708026826287379833848291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9138684550858253222565527 13708026826287379833848291)
                ·
                  refine ⟨20562040239431069750772437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13708026826287379833848291 20562040239431069750772437)
                  ·
                    refine ⟨481922818111665697283729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 20562040239431069750772437 481922818111665697283729)
                    ·
                      rfl

theorem cell23_2815624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 1, 1, 1, 7].length) (baseStart_2815624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2815624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2815624 prefixEnd_2815624 := by exact prefixLift 2815624
  have htrace : WordTrace (prefixWord ++ tailWord_2815624) baseStart_2815624 baseEnd_2815624 := by
    simpa [prefixWord, tailWord_2815624, baseEnd_2815624] using wordTrace_append hprefix tailTrace_2815624
  have hstable : (prefixWord ++ tailWord_2815624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2815624).length < 2 ^ (prefixWord ++ tailWord_2815624).sum := by decide
  have hdescent : baseEnd_2815624 < baseStart_2815624 := by decide
  rcases family_descends (prefixWord ++ tailWord_2815624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2815627 : List Nat := [1, 1, 1, 1, 4, 1, 3, 2, 1, 6, 2]
def baseStart_2815627 : Nat := 118140960795 + 2815627 * 2 ^ 59
def prefixEnd_2815627 : Nat := 4983230072969 + 3 ^ 40 * 2815627 * 2
def baseEnd_2815627 : Nat := 1445769994776960580113673

theorem tailTrace_2815627 : CollatzResearch.WordTrace tailWord_2815627 prefixEnd_2815627 1445769994776960580113673 := by
  unfold tailWord_2815627
  simp only [CollatzResearch.WordTrace]
  refine ⟨102694353370471724652629135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68462902246981149768419423 102694353370471724652629135)
  ·
    refine ⟨154041530055707586978943703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102694353370471724652629135 154041530055707586978943703)
    ·
      refine ⟨231062295083561380468415555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154041530055707586978943703 231062295083561380468415555)
      ·
        refine ⟨346593442625342070702623333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 231062295083561380468415555 346593442625342070702623333)
        ·
          refine ⟨64986270492251638256741875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 346593442625342070702623333 64986270492251638256741875)
          ·
            refine ⟨97479405738377457385112813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64986270492251638256741875 97479405738377457385112813)
            ·
              refine ⟨36554777151891546519417305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 97479405738377457385112813 36554777151891546519417305)
              ·
                refine ⟨27416082863918659889562979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36554777151891546519417305 27416082863918659889562979)
                ·
                  refine ⟨41124124295877989834344469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27416082863918659889562979 41124124295877989834344469)
                  ·
                    refine ⟨1927693326369280773484897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 41124124295877989834344469 1927693326369280773484897)
                    ·
                      refine ⟨1445769994776960580113673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1927693326369280773484897 1445769994776960580113673)
                      ·
                        rfl

theorem cell23_2815627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 2, 1, 6, 2].length) (baseStart_2815627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2815627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2815627 prefixEnd_2815627 := by exact prefixLift 2815627
  have htrace : WordTrace (prefixWord ++ tailWord_2815627) baseStart_2815627 baseEnd_2815627 := by
    simpa [prefixWord, tailWord_2815627, baseEnd_2815627] using wordTrace_append hprefix tailTrace_2815627
  have hstable : (prefixWord ++ tailWord_2815627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2815627).length < 2 ^ (prefixWord ++ tailWord_2815627).sum := by decide
  have hdescent : baseEnd_2815627 < baseStart_2815627 := by decide
  rcases family_descends (prefixWord ++ tailWord_2815627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2815677 : List Nat := [1, 4, 1, 2, 1, 2, 1, 1, 2, 5, 3]
def baseStart_2815677 : Nat := 118140960795 + 2815677 * 2 ^ 59
def prefixEnd_2815677 : Nat := 4983230072969 + 3 ^ 40 * 2815677 * 2
def baseEnd_2815677 : Nat := 1445795668809685384488443

theorem tailTrace_2815677 : CollatzResearch.WordTrace tailWord_2815677 prefixEnd_2815677 1445795668809685384488443 := by
  unfold tailWord_2815677
  simp only [CollatzResearch.WordTrace]
  refine ⟨102696177020290583191949285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68464118013527055461299523 102696177020290583191949285)
  ·
    refine ⟨19255533191304484348490491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 102696177020290583191949285 19255533191304484348490491)
    ·
      refine ⟨28883299786956726522735737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19255533191304484348490491 28883299786956726522735737)
      ·
        refine ⟨21662474840217544892051803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28883299786956726522735737 21662474840217544892051803)
        ·
          refine ⟨32493712260326317338077705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21662474840217544892051803 32493712260326317338077705)
          ·
            refine ⟨24370284195244738003558279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32493712260326317338077705 24370284195244738003558279)
            ·
              refine ⟨36555426292867107005337419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24370284195244738003558279 36555426292867107005337419)
              ·
                refine ⟨54833139439300660508006129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36555426292867107005337419 54833139439300660508006129)
                ·
                  refine ⟨41124854579475495381004597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54833139439300660508006129 41124854579475495381004597)
                  ·
                    refine ⟨3855455116825827691969181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 41124854579475495381004597 3855455116825827691969181)
                    ·
                      refine ⟨1445795668809685384488443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3855455116825827691969181 1445795668809685384488443)
                      ·
                        rfl

theorem cell23_2815677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 1, 2, 5, 3].length) (baseStart_2815677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2815677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2815677 prefixEnd_2815677 := by exact prefixLift 2815677
  have htrace : WordTrace (prefixWord ++ tailWord_2815677) baseStart_2815677 baseEnd_2815677 := by
    simpa [prefixWord, tailWord_2815677, baseEnd_2815677] using wordTrace_append hprefix tailTrace_2815677
  have hstable : (prefixWord ++ tailWord_2815677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2815677).length < 2 ^ (prefixWord ++ tailWord_2815677).sum := by decide
  have hdescent : baseEnd_2815677 < baseStart_2815677 := by decide
  rcases family_descends (prefixWord ++ tailWord_2815677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2815727 : List Nat := [1, 1, 2, 1, 5, 1, 2, 3, 1, 6]
def baseStart_2815727 : Nat := 118140960795 + 2815727 * 2 ^ 59
def prefixEnd_2815727 : Nat := 4983230072969 + 3 ^ 40 * 2815727 * 2
def baseEnd_2815727 : Nat := 481940447614136729621071

theorem tailTrace_2815727 : CollatzResearch.WordTrace tailWord_2815727 prefixEnd_2815727 481940447614136729621071 := by
  unfold tailWord_2815727
  simp only [CollatzResearch.WordTrace]
  refine ⟨102698000670109441731269435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68465333780072961154179623 102698000670109441731269435)
  ·
    refine ⟨154047001005164162596904153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102698000670109441731269435 154047001005164162596904153)
    ·
      refine ⟨115535250753873121947678115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154047001005164162596904153 115535250753873121947678115)
      ·
        refine ⟨173302876130809682921517173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115535250753873121947678115 173302876130809682921517173)
        ·
          refine ⟨16247144637263407773892235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 173302876130809682921517173 16247144637263407773892235)
          ·
            refine ⟨24370716955895111660838353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16247144637263407773892235 24370716955895111660838353)
            ·
              refine ⟨18278037716921333745628765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24370716955895111660838353 18278037716921333745628765)
              ·
                refine ⟨6854264143845500154610787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18278037716921333745628765 6854264143845500154610787)
                ·
                  refine ⟨10281396215768250231916181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6854264143845500154610787 10281396215768250231916181)
                  ·
                    refine ⟨481940447614136729621071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10281396215768250231916181 481940447614136729621071)
                    ·
                      rfl

theorem cell23_2815727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 3, 1, 6].length) (baseStart_2815727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2815727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2815727 prefixEnd_2815727 := by exact prefixLift 2815727
  have htrace : WordTrace (prefixWord ++ tailWord_2815727) baseStart_2815727 baseEnd_2815727 := by
    simpa [prefixWord, tailWord_2815727, baseEnd_2815727] using wordTrace_append hprefix tailTrace_2815727
  have hstable : (prefixWord ++ tailWord_2815727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2815727).length < 2 ^ (prefixWord ++ tailWord_2815727).sum := by decide
  have hdescent : baseEnd_2815727 < baseStart_2815727 := by decide
  rcases family_descends (prefixWord ++ tailWord_2815727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2815747 : List Nat := [1, 1, 1, 3, 2, 2, 3, 1, 3, 2, 4]
def baseStart_2815747 : Nat := 118140960795 + 2815747 * 2 ^ 59
def prefixEnd_2815747 : Nat := 4983230072969 + 3 ^ 40 * 2815747 * 2
def baseEnd_2815747 : Nat := 1445831612455500110613121

theorem tailTrace_2815747 : CollatzResearch.WordTrace tailWord_2815747 prefixEnd_2815747 1445831612455500110613121 := by
  unfold tailWord_2815747
  simp only [CollatzResearch.WordTrace]
  refine ⟨102698730130036985146997495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68465820086691323431331663 102698730130036985146997495)
  ·
    refine ⟨154048095195055477720496243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102698730130036985146997495 154048095195055477720496243)
    ·
      refine ⟨231072142792583216580744365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154048095195055477720496243 231072142792583216580744365)
      ·
        refine ⟨86652053547218706217779137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 231072142792583216580744365 86652053547218706217779137)
        ·
          refine ⟨64989040160414029663334353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86652053547218706217779137 64989040160414029663334353)
          ·
            refine ⟨48741780120310522247500765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64989040160414029663334353 48741780120310522247500765)
            ·
              refine ⟨18278167545116445842812787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48741780120310522247500765 18278167545116445842812787)
              ·
                refine ⟨27417251317674668764219181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18278167545116445842812787 27417251317674668764219181)
                ·
                  refine ⟨10281469244128000786582193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27417251317674668764219181 10281469244128000786582193)
                  ·
                    refine ⟨7711101933096000589936645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10281469244128000786582193 7711101933096000589936645)
                    ·
                      refine ⟨1445831612455500110613121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7711101933096000589936645 1445831612455500110613121)
                      ·
                        rfl

theorem cell23_2815747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 1, 3, 2, 4].length) (baseStart_2815747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2815747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2815747 prefixEnd_2815747 := by exact prefixLift 2815747
  have htrace : WordTrace (prefixWord ++ tailWord_2815747) baseStart_2815747 baseEnd_2815747 := by
    simpa [prefixWord, tailWord_2815747, baseEnd_2815747] using wordTrace_append hprefix tailTrace_2815747
  have hstable : (prefixWord ++ tailWord_2815747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2815747).length < 2 ^ (prefixWord ++ tailWord_2815747).sum := by decide
  have hdescent : baseEnd_2815747 < baseStart_2815747 := by decide
  rcases family_descends (prefixWord ++ tailWord_2815747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2815754 : List Nat := [3, 1, 2, 2, 1, 3, 3, 1, 1, 1, 5]
def baseStart_2815754 : Nat := 118140960795 + 2815754 * 2 ^ 59
def prefixEnd_2815754 : Nat := 4983230072969 + 3 ^ 40 * 2815754 * 2
def baseEnd_2815754 : Nat := 1445835206820081583225589

theorem tailTrace_2815754 : CollatzResearch.WordTrace tailWord_2815754 prefixEnd_2815754 1445835206820081583225589 := by
  unfold tailWord_2815754
  simp only [CollatzResearch.WordTrace]
  refine ⟨25674746360252906335625579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68465990294007750228334877 25674746360252906335625579)
  ·
    refine ⟨38512119540379359503438369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25674746360252906335625579 38512119540379359503438369)
    ·
      refine ⟨28884089655284519627578777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38512119540379359503438369 28884089655284519627578777)
      ·
        refine ⟨21663067241463389720684083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28884089655284519627578777 21663067241463389720684083)
        ·
          refine ⟨32494600862195084581026125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21663067241463389720684083 32494600862195084581026125)
          ·
            refine ⟨12185475323323156717884797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32494600862195084581026125 12185475323323156717884797)
            ·
              refine ⟨4569553246246183769206799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12185475323323156717884797 4569553246246183769206799)
              ·
                refine ⟨6854329869369275653810199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4569553246246183769206799 6854329869369275653810199)
                ·
                  refine ⟨10281494804053913480715299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6854329869369275653810199 10281494804053913480715299)
                  ·
                    refine ⟨15422242206080870221072949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10281494804053913480715299 15422242206080870221072949)
                    ·
                      refine ⟨1445835206820081583225589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15422242206080870221072949 1445835206820081583225589)
                      ·
                        rfl

theorem cell23_2815754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 3, 1, 1, 1, 5].length) (baseStart_2815754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2815754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2815754 prefixEnd_2815754 := by exact prefixLift 2815754
  have htrace : WordTrace (prefixWord ++ tailWord_2815754) baseStart_2815754 baseEnd_2815754 := by
    simpa [prefixWord, tailWord_2815754, baseEnd_2815754] using wordTrace_append hprefix tailTrace_2815754
  have hstable : (prefixWord ++ tailWord_2815754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2815754).length < 2 ^ (prefixWord ++ tailWord_2815754).sum := by decide
  have hdescent : baseEnd_2815754 < baseStart_2815754 := by decide
  rcases family_descends (prefixWord ++ tailWord_2815754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2815762 : List Nat := [3, 2, 4, 1, 1, 1, 4, 2, 1, 1, 3]
def baseStart_2815762 : Nat := 118140960795 + 2815762 * 2 ^ 59
def prefixEnd_2815762 : Nat := 4983230072969 + 3 ^ 40 * 2815762 * 2
def baseEnd_2815762 : Nat := 1445839314665317551925553

theorem tailTrace_2815762 : CollatzResearch.WordTrace tailWord_2815762 prefixEnd_2815762 1445839314665317551925553 := by
  unfold tailWord_2815762
  simp only [CollatzResearch.WordTrace]
  refine ⟨25674819306245660677198385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68466184816655095139195693 25674819306245660677198385)
  ·
    refine ⟨19256114479684245507898789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25674819306245660677198385 19256114479684245507898789)
    ·
      refine ⟨3610521464940796032731023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19256114479684245507898789 3610521464940796032731023)
      ·
        refine ⟨5415782197411194049096535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3610521464940796032731023 5415782197411194049096535)
        ·
          refine ⟨8123673296116791073644803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5415782197411194049096535 8123673296116791073644803)
          ·
            refine ⟨12185509944175186610467205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8123673296116791073644803 12185509944175186610467205)
            ·
              refine ⟨2284783114532847489462601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12185509944175186610467205 2284783114532847489462601)
              ·
                refine ⟨1713587335899635617096951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2284783114532847489462601 1713587335899635617096951)
                ·
                  refine ⟨2570381003849453425645427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1713587335899635617096951 2570381003849453425645427)
                  ·
                    refine ⟨3855571505774180138468141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2570381003849453425645427 3855571505774180138468141)
                    ·
                      refine ⟨1445839314665317551925553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3855571505774180138468141 1445839314665317551925553)
                      ·
                        rfl

theorem cell23_2815762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 4, 2, 1, 1, 3].length) (baseStart_2815762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2815762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2815762 prefixEnd_2815762 := by exact prefixLift 2815762
  have htrace : WordTrace (prefixWord ++ tailWord_2815762) baseStart_2815762 baseEnd_2815762 := by
    simpa [prefixWord, tailWord_2815762, baseEnd_2815762] using wordTrace_append hprefix tailTrace_2815762
  have hstable : (prefixWord ++ tailWord_2815762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2815762).length < 2 ^ (prefixWord ++ tailWord_2815762).sum := by decide
  have hdescent : baseEnd_2815762 < baseStart_2815762 := by decide
  rcases family_descends (prefixWord ++ tailWord_2815762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2815805 : List Nat := [1, 4, 1, 4, 1, 3, 2, 1, 1, 2, 3]
def baseStart_2815805 : Nat := 118140960795 + 2815805 * 2 ^ 59
def prefixEnd_2815805 : Nat := 4983230072969 + 3 ^ 40 * 2815805 * 2
def baseEnd_2815805 : Nat := 1445861394333460883687855

theorem tailTrace_2815805 : CollatzResearch.WordTrace tailWord_2815805 prefixEnd_2815805 1445861394333460883687855 := by
  unfold tailWord_2815805
  simp only [CollatzResearch.WordTrace]
  refine ⟨102700845563826861052608869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68467230375884574035072579 102700845563826861052608869)
  ·
    refine ⟨19256408543217536447364163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 102700845563826861052608869 19256408543217536447364163)
    ·
      refine ⟨28884612814826304671046245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19256408543217536447364163 28884612814826304671046245)
      ·
        refine ⟨5415864902779932125821171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28884612814826304671046245 5415864902779932125821171)
        ·
          refine ⟨8123797354169898188731757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5415864902779932125821171 8123797354169898188731757)
          ·
            refine ⟨3046424007813711820774409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8123797354169898188731757 3046424007813711820774409)
            ·
              refine ⟨2284818005860283865580807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3046424007813711820774409 2284818005860283865580807)
              ·
                refine ⟨3427227008790425798371211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2284818005860283865580807 3427227008790425798371211)
                ·
                  refine ⟨5140840513185638697556817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3427227008790425798371211 5140840513185638697556817)
                  ·
                    refine ⟨3855630384889229023167613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5140840513185638697556817 3855630384889229023167613)
                    ·
                      refine ⟨1445861394333460883687855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3855630384889229023167613 1445861394333460883687855)
                      ·
                        rfl

theorem cell23_2815805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 2, 1, 1, 2, 3].length) (baseStart_2815805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2815805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2815805 prefixEnd_2815805 := by exact prefixLift 2815805
  have htrace : WordTrace (prefixWord ++ tailWord_2815805) baseStart_2815805 baseEnd_2815805 := by
    simpa [prefixWord, tailWord_2815805, baseEnd_2815805] using wordTrace_append hprefix tailTrace_2815805
  have hstable : (prefixWord ++ tailWord_2815805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2815805).length < 2 ^ (prefixWord ++ tailWord_2815805).sum := by decide
  have hdescent : baseEnd_2815805 < baseStart_2815805 := by decide
  rcases family_descends (prefixWord ++ tailWord_2815805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2815817 : List Nat := [1, 2, 1, 1, 2, 4, 1, 1, 4, 6]
def baseStart_2815817 : Nat := 118140960795 + 2815817 * 2 ^ 59
def prefixEnd_2815817 : Nat := 4983230072969 + 3 ^ 40 * 2815817 * 2
def baseEnd_2815817 : Nat := 481955852033771612245933

theorem tailTrace_2815817 : CollatzResearch.WordTrace tailWord_2815817 prefixEnd_2815817 481955852033771612245933 := by
  unfold tailWord_2815817
  simp only [CollatzResearch.WordTrace]
  refine ⟨102701283239783387102045705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68467522159855591401363803 102701283239783387102045705)
  ·
    refine ⟨77025962429837540326534279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102701283239783387102045705 77025962429837540326534279)
    ·
      refine ⟨115538943644756310489801419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77025962429837540326534279 115538943644756310489801419)
      ·
        refine ⟨173308415467134465734702129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115538943644756310489801419 173308415467134465734702129)
        ·
          refine ⟨129981311600350849301026597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 173308415467134465734702129 129981311600350849301026597)
          ·
            refine ⟨24371495925065784243942487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 129981311600350849301026597 24371495925065784243942487)
            ·
              refine ⟨36557243887598676365913731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24371495925065784243942487 36557243887598676365913731)
              ·
                refine ⟨54835865831398014548870597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36557243887598676365913731 54835865831398014548870597)
                ·
                  refine ⟨10281724843387127727913237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 54835865831398014548870597 10281724843387127727913237)
                  ·
                    refine ⟨481955852033771612245933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10281724843387127727913237 481955852033771612245933)
                    ·
                      rfl

theorem cell23_2815817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 1, 4, 6].length) (baseStart_2815817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2815817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2815817 prefixEnd_2815817 := by exact prefixLift 2815817
  have htrace : WordTrace (prefixWord ++ tailWord_2815817) baseStart_2815817 baseEnd_2815817 := by
    simpa [prefixWord, tailWord_2815817, baseEnd_2815817] using wordTrace_append hprefix tailTrace_2815817
  have hstable : (prefixWord ++ tailWord_2815817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2815817).length < 2 ^ (prefixWord ++ tailWord_2815817).sum := by decide
  have hdescent : baseEnd_2815817 < baseStart_2815817 := by decide
  rcases family_descends (prefixWord ++ tailWord_2815817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2815827 : List Nat := [1, 1, 1, 2, 1, 1, 3, 1, 6, 1, 5]
def baseStart_2815827 : Nat := 118140960795 + 2815827 * 2 ^ 59
def prefixEnd_2815827 : Nat := 4983230072969 + 3 ^ 40 * 2815827 * 2
def baseEnd_2815827 : Nat := 1445872690907859797612753

theorem tailTrace_2815827 : CollatzResearch.WordTrace tailWord_2815827 prefixEnd_2815827 1445872690907859797612753 := by
  unfold tailWord_2815827
  simp only [CollatzResearch.WordTrace]
  refine ⟨102701647969747158809909735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68467765313164772539939823 102701647969747158809909735)
  ·
    refine ⟨154052471954620738214864603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102701647969747158809909735 154052471954620738214864603)
    ·
      refine ⟨231078707931931107322296905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154052471954620738214864603 231078707931931107322296905)
      ·
        refine ⟨173309030948948330491722679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 231078707931931107322296905 173309030948948330491722679)
        ·
          refine ⟨259963546423422495737584019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173309030948948330491722679 259963546423422495737584019)
          ·
            refine ⟨389945319635133743606376029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 259963546423422495737584019 389945319635133743606376029)
            ·
              refine ⟨146229494863175153852391011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 389945319635133743606376029 146229494863175153852391011)
              ·
                refine ⟨219344242294762730778586517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 146229494863175153852391011 219344242294762730778586517)
                ·
                  refine ⟨10281761357567003005246243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 219344242294762730778586517 10281761357567003005246243)
                  ·
                    refine ⟨15422642036350504507869365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10281761357567003005246243 15422642036350504507869365)
                    ·
                      refine ⟨1445872690907859797612753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15422642036350504507869365 1445872690907859797612753)
                      ·
                        rfl

theorem cell23_2815827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 6, 1, 5].length) (baseStart_2815827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2815827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2815827 prefixEnd_2815827 := by exact prefixLift 2815827
  have htrace : WordTrace (prefixWord ++ tailWord_2815827) baseStart_2815827 baseEnd_2815827 := by
    simpa [prefixWord, tailWord_2815827, baseEnd_2815827] using wordTrace_append hprefix tailTrace_2815827
  have hstable : (prefixWord ++ tailWord_2815827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2815827).length < 2 ^ (prefixWord ++ tailWord_2815827).sum := by decide
  have hdescent : baseEnd_2815827 < baseStart_2815827 := by decide
  rcases family_descends (prefixWord ++ tailWord_2815827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2815892 : List Nat := [2, 4, 2, 1, 1, 2, 4, 1, 2, 2, 2]
def baseStart_2815892 : Nat := 118140960795 + 2815892 * 2 ^ 59
def prefixEnd_2815892 : Nat := 4983230072969 + 3 ^ 40 * 2815892 * 2
def baseEnd_2815892 : Nat := 1445906067150402043299955

theorem tailTrace_2815892 : CollatzResearch.WordTrace tailWord_2815892 prefixEnd_2815892 1445906067150402043299955 := by
  unfold tailWord_2815892
  simp only [CollatzResearch.WordTrace]
  refine ⟨51352009357255837455512965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68469345809674449940683953 51352009357255837455512965)
  ·
    refine ⟨9628501754485469522908681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51352009357255837455512965 9628501754485469522908681)
    ·
      refine ⟨7221376315864102142181511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9628501754485469522908681 7221376315864102142181511)
      ·
        refine ⟨10832064473796153213272267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7221376315864102142181511 10832064473796153213272267)
        ·
          refine ⟨16248096710694229819908401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10832064473796153213272267 16248096710694229819908401)
          ·
            refine ⟨12186072533020672364931301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16248096710694229819908401 12186072533020672364931301)
            ·
              refine ⟨2284888599941376068424619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12186072533020672364931301 2284888599941376068424619)
              ·
                refine ⟨3427332899912064102636929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2284888599941376068424619 3427332899912064102636929)
                ·
                  refine ⟨2570499674934048076977697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3427332899912064102636929 2570499674934048076977697)
                  ·
                    refine ⟨1927874756200536057733273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2570499674934048076977697 1927874756200536057733273)
                    ·
                      refine ⟨1445906067150402043299955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1927874756200536057733273 1445906067150402043299955)
                      ·
                        rfl

theorem cell23_2815892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 4, 1, 2, 2, 2].length) (baseStart_2815892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2815892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2815892 prefixEnd_2815892 := by exact prefixLift 2815892
  have htrace : WordTrace (prefixWord ++ tailWord_2815892) baseStart_2815892 baseEnd_2815892 := by
    simpa [prefixWord, tailWord_2815892, baseEnd_2815892] using wordTrace_append hprefix tailTrace_2815892
  have hstable : (prefixWord ++ tailWord_2815892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2815892).length < 2 ^ (prefixWord ++ tailWord_2815892).sum := by decide
  have hdescent : baseEnd_2815892 < baseStart_2815892 := by decide
  rcases family_descends (prefixWord ++ tailWord_2815892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2815911 : List Nat := [1, 1, 6, 1, 2, 1, 1, 3, 2, 5]
def baseStart_2815911 : Nat := 118140960795 + 2815911 * 2 ^ 59
def prefixEnd_2815911 : Nat := 4983230072969 + 3 ^ 40 * 2815911 * 2
def baseEnd_2815911 : Nat := 481971941094279156320789

theorem tailTrace_2815911 : CollatzResearch.WordTrace tailWord_2815911 prefixEnd_2815911 481971941094279156320789 := by
  unfold tailWord_2815911
  simp only [CollatzResearch.WordTrace]
  refine ⟨102704711701442841155967587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68469807800961894103978391 102704711701442841155967587)
  ·
    refine ⟨154057067552164261733951381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102704711701442841155967587 154057067552164261733951381)
    ·
      refine ⟨7221425041507699768778971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 154057067552164261733951381 7221425041507699768778971)
      ·
        refine ⟨10832137562261549653168457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7221425041507699768778971 10832137562261549653168457)
        ·
          refine ⟨8124103171696162239876343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10832137562261549653168457 8124103171696162239876343)
          ·
            refine ⟨12186154757544243359814515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8124103171696162239876343 12186154757544243359814515)
            ·
              refine ⟨18279232136316365039721773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12186154757544243359814515 18279232136316365039721773)
              ·
                refine ⟨6854712051118636889895665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18279232136316365039721773 6854712051118636889895665)
                ·
                  refine ⟨5141034038338977667421749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6854712051118636889895665 5141034038338977667421749)
                  ·
                    refine ⟨481971941094279156320789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5141034038338977667421749 481971941094279156320789)
                    ·
                      rfl

theorem cell23_2815911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 3, 2, 5].length) (baseStart_2815911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2815911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2815911 prefixEnd_2815911 := by exact prefixLift 2815911
  have htrace : WordTrace (prefixWord ++ tailWord_2815911) baseStart_2815911 baseEnd_2815911 := by
    simpa [prefixWord, tailWord_2815911, baseEnd_2815911] using wordTrace_append hprefix tailTrace_2815911
  have hstable : (prefixWord ++ tailWord_2815911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2815911).length < 2 ^ (prefixWord ++ tailWord_2815911).sum := by decide
  have hdescent : baseEnd_2815911 < baseStart_2815911 := by decide
  rcases family_descends (prefixWord ++ tailWord_2815911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2815932 : List Nat := [2, 2, 2, 5, 1, 2, 2, 2, 5]
def baseStart_2815932 : Nat := 118140960795 + 2815932 * 2 ^ 59
def prefixEnd_2815932 : Nat := 4983230072969 + 3 ^ 40 * 2815932 * 2
def baseEnd_2815932 : Nat := 160658511819620209644419

theorem tailTrace_2815932 : CollatzResearch.WordTrace tailWord_2815932 prefixEnd_2815932 160658511819620209644419 := by
  unfold tailWord_2815932
  simp only [CollatzResearch.WordTrace]
  refine ⟨51352738817183380871241025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68470318422911174494988033 51352738817183380871241025)
  ·
    refine ⟨38514554112887535653430769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51352738817183380871241025 38514554112887535653430769)
    ·
      refine ⟨28885915584665651740073077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38514554112887535653430769 28885915584665651740073077)
      ·
        refine ⟨2708054586062404850631851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 28885915584665651740073077 2708054586062404850631851)
        ·
          refine ⟨4062081879093607275947777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2708054586062404850631851 4062081879093607275947777)
          ·
            refine ⟨3046561409320205456960833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4062081879093607275947777 3046561409320205456960833)
            ·
              refine ⟨2284921056990154092720625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3046561409320205456960833 2284921056990154092720625)
              ·
                refine ⟨1713690792742615569540469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2284921056990154092720625 1713690792742615569540469)
                ·
                  refine ⟨160658511819620209644419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1713690792742615569540469 160658511819620209644419)
                  ·
                    rfl

theorem cell23_2815932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 2, 2, 5].length) (baseStart_2815932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2815932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2815932 prefixEnd_2815932 := by exact prefixLift 2815932
  have htrace : WordTrace (prefixWord ++ tailWord_2815932) baseStart_2815932 baseEnd_2815932 := by
    simpa [prefixWord, tailWord_2815932, baseEnd_2815932] using wordTrace_append hprefix tailTrace_2815932
  have hstable : (prefixWord ++ tailWord_2815932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2815932).length < 2 ^ (prefixWord ++ tailWord_2815932).sum := by decide
  have hdescent : baseEnd_2815932 < baseStart_2815932 := by decide
  rcases family_descends (prefixWord ++ tailWord_2815932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2815948 : List Nat := [2, 2, 1, 4, 1, 3, 1, 1, 2, 4, 2]
def baseStart_2815948 : Nat := 118140960795 + 2815948 * 2 ^ 59
def prefixEnd_2815948 : Nat := 4983230072969 + 3 ^ 40 * 2815948 * 2
def baseEnd_2815948 : Nat := 1445934822067053824199697

theorem tailTrace_2815948 : CollatzResearch.WordTrace tailWord_2815948 prefixEnd_2815948 1445934822067053824199697 := by
  unfold tailWord_2815948
  simp only [CollatzResearch.WordTrace]
  refine ⟨51353030601154398237532249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68470707468205864316709665 51353030601154398237532249)
  ·
    refine ⟨38514772950865798678149187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51353030601154398237532249 38514772950865798678149187)
    ·
      refine ⟨57772159426298698017223781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38514772950865798678149187 57772159426298698017223781)
      ·
        refine ⟨10832279892431005878229459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57772159426298698017223781 10832279892431005878229459)
        ·
          refine ⟨16248419838646508817344189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10832279892431005878229459 16248419838646508817344189)
          ·
            refine ⟨6093157439492440806504071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16248419838646508817344189 6093157439492440806504071)
            ·
              refine ⟨9139736159238661209756107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6093157439492440806504071 9139736159238661209756107)
              ·
                refine ⟨13709604238857991814634161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9139736159238661209756107 13709604238857991814634161)
                ·
                  refine ⟨10282203179143493860975621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13709604238857991814634161 10282203179143493860975621)
                  ·
                    refine ⟨1927913096089405098932929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10282203179143493860975621 1927913096089405098932929)
                    ·
                      refine ⟨1445934822067053824199697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1927913096089405098932929 1445934822067053824199697)
                      ·
                        rfl

theorem cell23_2815948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 1, 1, 2, 4, 2].length) (baseStart_2815948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2815948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2815948 prefixEnd_2815948 := by exact prefixLift 2815948
  have htrace : WordTrace (prefixWord ++ tailWord_2815948) baseStart_2815948 baseEnd_2815948 := by
    simpa [prefixWord, tailWord_2815948, baseEnd_2815948] using wordTrace_append hprefix tailTrace_2815948
  have hstable : (prefixWord ++ tailWord_2815948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2815948).length < 2 ^ (prefixWord ++ tailWord_2815948).sum := by decide
  have hdescent : baseEnd_2815948 < baseStart_2815948 := by decide
  rcases family_descends (prefixWord ++ tailWord_2815948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2815965 : List Nat := [1, 4, 3, 1, 3, 2, 1, 1, 2, 1, 4]
def baseStart_2815965 : Nat := 118140960795 + 2815965 * 2 ^ 59
def prefixEnd_2815965 : Nat := 4983230072969 + 3 ^ 40 * 2815965 * 2
def baseEnd_2815965 : Nat := 1445943551238180257687119

theorem tailTrace_2815965 : CollatzResearch.WordTrace tailWord_2815965 prefixEnd_2815965 1445943551238180257687119 := by
  unfold tailWord_2815965
  simp only [CollatzResearch.WordTrace]
  refine ⟨102706681243247208378433349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68471120828831472252288899 102706681243247208378433349)
  ·
    refine ⟨19257502733108851570956253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 102706681243247208378433349 19257502733108851570956253)
    ·
      refine ⟨7221563524915819339108595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19257502733108851570956253 7221563524915819339108595)
      ·
        refine ⟨10832345287373729008662893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7221563524915819339108595 10832345287373729008662893)
        ·
          refine ⟨4062129482765148378248585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10832345287373729008662893 4062129482765148378248585)
          ·
            refine ⟨3046597112073861283686439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4062129482765148378248585 3046597112073861283686439)
            ·
              refine ⟨4569895668110791925529659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3046597112073861283686439 4569895668110791925529659)
              ·
                refine ⟨6854843502166187888294489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4569895668110791925529659 6854843502166187888294489)
                ·
                  refine ⟨5141132626624640916220867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6854843502166187888294489 5141132626624640916220867)
                  ·
                    refine ⟨7711698939936961374331301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5141132626624640916220867 7711698939936961374331301)
                    ·
                      refine ⟨1445943551238180257687119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7711698939936961374331301 1445943551238180257687119)
                      ·
                        rfl

theorem cell23_2815965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 1, 1, 2, 1, 4].length) (baseStart_2815965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2815965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2815965 prefixEnd_2815965 := by exact prefixLift 2815965
  have htrace : WordTrace (prefixWord ++ tailWord_2815965) baseStart_2815965 baseEnd_2815965 := by
    simpa [prefixWord, tailWord_2815965, baseEnd_2815965] using wordTrace_append hprefix tailTrace_2815965
  have hstable : (prefixWord ++ tailWord_2815965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2815965).length < 2 ^ (prefixWord ++ tailWord_2815965).sum := by decide
  have hdescent : baseEnd_2815965 < baseStart_2815965 := by decide
  rcases family_descends (prefixWord ++ tailWord_2815965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2816031 : List Nat := [1, 1, 2, 4, 1, 2, 1, 1, 6, 4]
def baseStart_2816031 : Nat := 118140960795 + 2816031 * 2 ^ 59
def prefixEnd_2816031 : Nat := 4983230072969 + 3 ^ 40 * 2816031 * 2
def baseEnd_2816031 : Nat := 481992480320458999820605

theorem tailTrace_2816031 : CollatzResearch.WordTrace tailWord_2816031 prefixEnd_2816031 481992480320458999820605 := by
  unfold tailWord_2816031
  simp only [CollatzResearch.WordTrace]
  refine ⟨102709088461008101650335947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68472725640672067766890631 102709088461008101650335947)
  ·
    refine ⟨154063632691512152475503921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102709088461008101650335947 154063632691512152475503921)
    ·
      refine ⟨115547724518634114356627941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154063632691512152475503921 115547724518634114356627941)
      ·
        refine ⟨21665198347243896441867739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 115547724518634114356627941 21665198347243896441867739)
        ·
          refine ⟨32497797520865844662801609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21665198347243896441867739 32497797520865844662801609)
          ·
            refine ⟨24373348140649383497101207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32497797520865844662801609 24373348140649383497101207)
            ·
              refine ⟨36560022210974075245651811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24373348140649383497101207 36560022210974075245651811)
              ·
                refine ⟨54840033316461112868477717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36560022210974075245651811 54840033316461112868477717)
                ·
                  refine ⟨2570626561709114665709893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 54840033316461112868477717 2570626561709114665709893)
                  ·
                    refine ⟨481992480320458999820605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2570626561709114665709893 481992480320458999820605)
                    ·
                      rfl

theorem cell23_2816031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 1, 6, 4].length) (baseStart_2816031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2816031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2816031 prefixEnd_2816031 := by exact prefixLift 2816031
  have htrace : WordTrace (prefixWord ++ tailWord_2816031) baseStart_2816031 baseEnd_2816031 := by
    simpa [prefixWord, tailWord_2816031, baseEnd_2816031] using wordTrace_append hprefix tailTrace_2816031
  have hstable : (prefixWord ++ tailWord_2816031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2816031).length < 2 ^ (prefixWord ++ tailWord_2816031).sum := by decide
  have hdescent : baseEnd_2816031 < baseStart_2816031 := by decide
  rcases family_descends (prefixWord ++ tailWord_2816031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2816055 : List Nat := [1, 1, 3, 1, 2, 2, 5, 1, 3, 2, 2]
def baseStart_2816055 : Nat := 118140960795 + 2816055 * 2 ^ 59
def prefixEnd_2816055 : Nat := 4983230072969 + 3 ^ 40 * 2816055 * 2
def baseEnd_2816055 : Nat := 1445989764497084905561705

theorem tailTrace_2816055 : CollatzResearch.WordTrace tailWord_2816055 prefixEnd_2816055 1445989764497084905561705 := by
  unfold tailWord_2816055
  simp only [CollatzResearch.WordTrace]
  refine ⟨102709963812921153749209619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68473309208614102499473079 102709963812921153749209619)
  ·
    refine ⟨154064945719381730623814429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102709963812921153749209619 154064945719381730623814429)
    ·
      refine ⟨57774354644768148983930411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 154064945719381730623814429 57774354644768148983930411)
      ·
        refine ⟨86661531967152223475895617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57774354644768148983930411 86661531967152223475895617)
        ·
          refine ⟨64996148975364167606921713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86661531967152223475895617 64996148975364167606921713)
          ·
            refine ⟨48747111731523125705191285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64996148975364167606921713 48747111731523125705191285)
            ·
              refine ⟨4570041724830293034861683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 48747111731523125705191285 4570041724830293034861683)
              ·
                refine ⟨6855062587245439552292525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4570041724830293034861683 6855062587245439552292525)
                ·
                  refine ⟨2570648470217039832109697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6855062587245439552292525 2570648470217039832109697)
                  ·
                    refine ⟨1927986352662779874082273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2570648470217039832109697 1927986352662779874082273)
                    ·
                      refine ⟨1445989764497084905561705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1927986352662779874082273 1445989764497084905561705)
                      ·
                        rfl

theorem cell23_2816055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 5, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 5, 1, 3, 2, 2].length) (baseStart_2816055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2816055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2816055 prefixEnd_2816055 := by exact prefixLift 2816055
  have htrace : WordTrace (prefixWord ++ tailWord_2816055) baseStart_2816055 baseEnd_2816055 := by
    simpa [prefixWord, tailWord_2816055, baseEnd_2816055] using wordTrace_append hprefix tailTrace_2816055
  have hstable : (prefixWord ++ tailWord_2816055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2816055).length < 2 ^ (prefixWord ++ tailWord_2816055).sum := by decide
  have hdescent : baseEnd_2816055 < baseStart_2816055 := by decide
  rcases family_descends (prefixWord ++ tailWord_2816055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2816061 : List Nat := [1, 4, 1, 3, 1, 1, 4, 8]
def baseStart_2816061 : Nat := 118140960795 + 2816061 * 2 ^ 59
def prefixEnd_2816061 : Nat := 4983230072969 + 3 ^ 40 * 2816061 * 2
def baseEnd_2816061 : Nat := 53555290569667106743951

theorem tailTrace_2816061 : CollatzResearch.WordTrace tailWord_2816061 prefixEnd_2816061 53555290569667106743951 := by
  unfold tailWord_2816061
  simp only [CollatzResearch.WordTrace]
  refine ⟨102710182650899416773928037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68473455100599611182618691 102710182650899416773928037)
  ·
    refine ⟨19258159247043640645111507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 102710182650899416773928037 19258159247043640645111507)
    ·
      refine ⟨28887238870565460967667261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19258159247043640645111507 28887238870565460967667261)
      ·
        refine ⟨10832714576462047862875223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28887238870565460967667261 10832714576462047862875223)
        ·
          refine ⟨16249071864693071794312835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10832714576462047862875223 16249071864693071794312835)
          ·
            refine ⟨24373607797039607691469253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16249071864693071794312835 24373607797039607691469253)
            ·
              refine ⟨4570051461944926442150485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24373607797039607691469253 4570051461944926442150485)
              ·
                refine ⟨53555290569667106743951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4570051461944926442150485 53555290569667106743951)
                ·
                  rfl

theorem cell23_2816061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 4, 8].length) (baseStart_2816061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2816061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2816061 prefixEnd_2816061 := by exact prefixLift 2816061
  have htrace : WordTrace (prefixWord ++ tailWord_2816061) baseStart_2816061 baseEnd_2816061 := by
    simpa [prefixWord, tailWord_2816061, baseEnd_2816061] using wordTrace_append hprefix tailTrace_2816061
  have hstable : (prefixWord ++ tailWord_2816061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2816061).length < 2 ^ (prefixWord ++ tailWord_2816061).sum := by decide
  have hdescent : baseEnd_2816061 < baseStart_2816061 := by decide
  rcases family_descends (prefixWord ++ tailWord_2816061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2816065 : List Nat := [1, 2, 5, 1, 2, 2, 1, 3, 2, 4]
def baseStart_2816065 : Nat := 118140960795 + 2816065 * 2 ^ 59
def prefixEnd_2816065 : Nat := 4983230072969 + 3 ^ 40 * 2816065 * 2
def baseEnd_2816065 : Nat := 481998299767876622145553

theorem tailTrace_2816065 : CollatzResearch.WordTrace tailWord_2816065 prefixEnd_2816065 481998299767876622145553 := by
  unfold tailWord_2816065
  simp only [CollatzResearch.WordTrace]
  refine ⟨102710328542884925457073649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68473552361923283638049099 102710328542884925457073649)
  ·
    refine ⟨77032746407163694092805237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102710328542884925457073649 77032746407163694092805237)
    ·
      refine ⟨7221819975671596321200491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 77032746407163694092805237 7221819975671596321200491)
      ·
        refine ⟨10832729963507394481800737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7221819975671596321200491 10832729963507394481800737)
        ·
          refine ⟨8124547472630545861350553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10832729963507394481800737 8124547472630545861350553)
          ·
            refine ⟨6093410604472909396012915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8124547472630545861350553 6093410604472909396012915)
            ·
              refine ⟨9140115906709364094019373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6093410604472909396012915 9140115906709364094019373)
              ·
                refine ⟨3427543465016011535257265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9140115906709364094019373 3427543465016011535257265)
                ·
                  refine ⟨2570657598762008651442949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3427543465016011535257265 2570657598762008651442949)
                  ·
                    refine ⟨481998299767876622145553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2570657598762008651442949 481998299767876622145553)
                    ·
                      rfl

theorem cell23_2816065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 1, 3, 2, 4].length) (baseStart_2816065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2816065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2816065 prefixEnd_2816065 := by exact prefixLift 2816065
  have htrace : WordTrace (prefixWord ++ tailWord_2816065) baseStart_2816065 baseEnd_2816065 := by
    simpa [prefixWord, tailWord_2816065, baseEnd_2816065] using wordTrace_append hprefix tailTrace_2816065
  have hstable : (prefixWord ++ tailWord_2816065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2816065).length < 2 ^ (prefixWord ++ tailWord_2816065).sum := by decide
  have hdescent : baseEnd_2816065 < baseStart_2816065 := by decide
  rcases family_descends (prefixWord ++ tailWord_2816065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2816088 : List Nat := [2, 1, 2, 2, 1, 5, 1, 2, 1, 3, 3]
def baseStart_2816088 : Nat := 118140960795 + 2816088 * 2 ^ 59
def prefixEnd_2816088 : Nat := 4983230072969 + 3 ^ 40 * 2816088 * 2
def baseEnd_2816088 : Nat := 1446006709358683276449053

theorem tailTrace_2816088 : CollatzResearch.WordTrace tailWord_2816088 prefixEnd_2816088 1446006709358683276449053 := by
  unfold tailWord_2816088
  simp only [CollatzResearch.WordTrace]
  refine ⟨51355583710900800192580459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68474111614534400256773945 51355583710900800192580459)
  ·
    refine ⟨77033375566351200288870689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51355583710900800192580459 77033375566351200288870689)
    ·
      refine ⟨57775031674763400216653017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77033375566351200288870689 57775031674763400216653017)
      ·
        refine ⟨43331273756072550162489763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57775031674763400216653017 43331273756072550162489763)
        ·
          refine ⟨64996910634108825243734645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43331273756072550162489763 64996910634108825243734645)
          ·
            refine ⟨6093460371947702366600123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 64996910634108825243734645 6093460371947702366600123)
            ·
              refine ⟨9140190557921553549900185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6093460371947702366600123 9140190557921553549900185)
              ·
                refine ⟨6855142918441165162425139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9140190557921553549900185 6855142918441165162425139)
                ·
                  refine ⟨10282714377661747743637709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6855142918441165162425139 10282714377661747743637709)
                  ·
                    refine ⟨3856017891623155403864141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10282714377661747743637709 3856017891623155403864141)
                    ·
                      refine ⟨1446006709358683276449053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3856017891623155403864141 1446006709358683276449053)
                      ·
                        rfl

theorem cell23_2816088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 1, 2, 1, 3, 3].length) (baseStart_2816088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2816088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2816088 prefixEnd_2816088 := by exact prefixLift 2816088
  have htrace : WordTrace (prefixWord ++ tailWord_2816088) baseStart_2816088 baseEnd_2816088 := by
    simpa [prefixWord, tailWord_2816088, baseEnd_2816088] using wordTrace_append hprefix tailTrace_2816088
  have hstable : (prefixWord ++ tailWord_2816088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2816088).length < 2 ^ (prefixWord ++ tailWord_2816088).sum := by decide
  have hdescent : baseEnd_2816088 < baseStart_2816088 := by decide
  rcases family_descends (prefixWord ++ tailWord_2816088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2816092 : List Nat := [2, 2, 4, 1, 1, 3, 3, 1, 1, 2, 3]
def baseStart_2816092 : Nat := 118140960795 + 2816092 * 2 ^ 59
def prefixEnd_2816092 : Nat := 4983230072969 + 3 ^ 40 * 2816092 * 2
def baseEnd_2816092 : Nat := 1446008763281301260799035

theorem tailTrace_2816092 : CollatzResearch.WordTrace tailWord_2816092 prefixEnd_2816092 1446008763281301260799035 := by
  unfold tailWord_2816092
  simp only [CollatzResearch.WordTrace]
  refine ⟨51355656656893554534153265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68474208875858072712204353 51355656656893554534153265)
  ·
    refine ⟨38516742492670165900614949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51355656656893554534153265 38516742492670165900614949)
    ·
      refine ⟨7221889217375656106365303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38516742492670165900614949 7221889217375656106365303)
      ·
        refine ⟨10832833826063484159547955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7221889217375656106365303 10832833826063484159547955)
        ·
          refine ⟨16249250739095226239321933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10832833826063484159547955 16249250739095226239321933)
          ·
            refine ⟨6093469027160709839745725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16249250739095226239321933 6093469027160709839745725)
            ·
              refine ⟨2285050885185266189904647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6093469027160709839745725 2285050885185266189904647)
              ·
                refine ⟨3427576327777899284856971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2285050885185266189904647 3427576327777899284856971)
                ·
                  refine ⟨5141364491666848927285457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3427576327777899284856971 5141364491666848927285457)
                  ·
                    refine ⟨3856023368750136695464093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5141364491666848927285457 3856023368750136695464093)
                    ·
                      refine ⟨1446008763281301260799035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3856023368750136695464093 1446008763281301260799035)
                      ·
                        rfl

theorem cell23_2816092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 3, 1, 1, 2, 3].length) (baseStart_2816092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2816092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2816092 prefixEnd_2816092 := by exact prefixLift 2816092
  have htrace : WordTrace (prefixWord ++ tailWord_2816092) baseStart_2816092 baseEnd_2816092 := by
    simpa [prefixWord, tailWord_2816092, baseEnd_2816092] using wordTrace_append hprefix tailTrace_2816092
  have hstable : (prefixWord ++ tailWord_2816092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2816092).length < 2 ^ (prefixWord ++ tailWord_2816092).sum := by decide
  have hdescent : baseEnd_2816092 < baseStart_2816092 := by decide
  rcases family_descends (prefixWord ++ tailWord_2816092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2816105 : List Nat := [1, 2, 1, 1, 1, 5, 4, 2, 2, 1, 3]
def baseStart_2816105 : Nat := 118140960795 + 2816105 * 2 ^ 59
def prefixEnd_2816105 : Nat := 4983230072969 + 3 ^ 40 * 2816105 * 2
def baseEnd_2816105 : Nat := 1446015438529809709936475

theorem tailTrace_2816105 : CollatzResearch.WordTrace tailWord_2816105 prefixEnd_2816105 1446015438529809709936475 := by
  unfold tailWord_2816105
  simp only [CollatzResearch.WordTrace]
  refine ⟨102711787462740012288529769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68474524975160008192353179 102711787462740012288529769)
  ·
    refine ⟨77033840597055009216397327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102711787462740012288529769 77033840597055009216397327)
    ·
      refine ⟨115550760895582513824595991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77033840597055009216397327 115550760895582513824595991)
      ·
        refine ⟨173326141343373770736893987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115550760895582513824595991 173326141343373770736893987)
        ·
          refine ⟨259989212015060656105340981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173326141343373770736893987 259989212015060656105340981)
          ·
            refine ⟨24373988626411936509875717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 259989212015060656105340981 24373988626411936509875717)
            ·
              refine ⟨4570122867452238095601697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24373988626411936509875717 4570122867452238095601697)
              ·
                refine ⟨3427592150589178571701273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4570122867452238095601697 3427592150589178571701273)
                ·
                  refine ⟨2570694112941883928775955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3427592150589178571701273 2570694112941883928775955)
                  ·
                    refine ⟨3856041169412825893163933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2570694112941883928775955 3856041169412825893163933)
                    ·
                      refine ⟨1446015438529809709936475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3856041169412825893163933 1446015438529809709936475)
                      ·
                        rfl

theorem cell23_2816105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 4, 2, 2, 1, 3].length) (baseStart_2816105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2816105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2816105 prefixEnd_2816105 := by exact prefixLift 2816105
  have htrace : WordTrace (prefixWord ++ tailWord_2816105) baseStart_2816105 baseEnd_2816105 := by
    simpa [prefixWord, tailWord_2816105, baseEnd_2816105] using wordTrace_append hprefix tailTrace_2816105
  have hstable : (prefixWord ++ tailWord_2816105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2816105).length < 2 ^ (prefixWord ++ tailWord_2816105).sum := by decide
  have hdescent : baseEnd_2816105 < baseStart_2816105 := by decide
  rcases family_descends (prefixWord ++ tailWord_2816105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2816111 : List Nat := [1, 1, 2, 1, 3, 4, 1, 1, 2, 3, 4]
def baseStart_2816111 : Nat := 118140960795 + 2816111 * 2 ^ 59
def prefixEnd_2816111 : Nat := 4983230072969 + 3 ^ 40 * 2816111 * 2
def baseEnd_2816111 : Nat := 1446018519413736686461447

theorem tailTrace_2816111 : CollatzResearch.WordTrace tailWord_2816111 prefixEnd_2816111 1446018519413736686461447 := by
  unfold tailWord_2816111
  simp only [CollatzResearch.WordTrace]
  refine ⟨102712006300718275313248187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68474670867145516875498791 102712006300718275313248187)
  ·
    refine ⟨154068009451077412969872281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102712006300718275313248187 154068009451077412969872281)
    ·
      refine ⟨115551007088308059727404211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154068009451077412969872281 115551007088308059727404211)
      ·
        refine ⟨173326510632462089591106317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115551007088308059727404211 173326510632462089591106317)
        ·
          refine ⟨64997441487173283596664869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 173326510632462089591106317 64997441487173283596664869)
          ·
            refine ⟨12187020278844990674374663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 64997441487173283596664869 12187020278844990674374663)
            ·
              refine ⟨18280530418267486011561995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12187020278844990674374663 18280530418267486011561995)
              ·
                refine ⟨27420795627401229017342993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18280530418267486011561995 27420795627401229017342993)
                ·
                  refine ⟨20565596720550921763007245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27420795627401229017342993 20565596720550921763007245)
                  ·
                    refine ⟨7712098770206595661127717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20565596720550921763007245 7712098770206595661127717)
                    ·
                      refine ⟨1446018519413736686461447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7712098770206595661127717 1446018519413736686461447)
                      ·
                        rfl

theorem cell23_2816111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 1, 2, 3, 4].length) (baseStart_2816111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2816111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2816111 prefixEnd_2816111 := by exact prefixLift 2816111
  have htrace : WordTrace (prefixWord ++ tailWord_2816111) baseStart_2816111 baseEnd_2816111 := by
    simpa [prefixWord, tailWord_2816111, baseEnd_2816111] using wordTrace_append hprefix tailTrace_2816111
  have hstable : (prefixWord ++ tailWord_2816111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2816111).length < 2 ^ (prefixWord ++ tailWord_2816111).sum := by decide
  have hdescent : baseEnd_2816111 < baseStart_2816111 := by decide
  rcases family_descends (prefixWord ++ tailWord_2816111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2816121 : List Nat := [1, 2, 1, 3, 4, 1, 1, 1, 1, 8]
def baseStart_2816121 : Nat := 118140960795 + 2816121 * 2 ^ 59
def prefixEnd_2816121 : Nat := 4983230072969 + 3 ^ 40 * 2816121 * 2
def baseEnd_2816121 : Nat := 482007884740093882445467

theorem tailTrace_2816121 : CollatzResearch.WordTrace tailWord_2816121 prefixEnd_2816121 482007884740093882445467 := by
  unfold tailWord_2816121
  simp only [CollatzResearch.WordTrace]
  refine ⟨102712371030682047021112217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68474914020454698014074811 102712371030682047021112217)
  ·
    refine ⟨77034278273011535265834163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102712371030682047021112217 77034278273011535265834163)
    ·
      refine ⟨115551417409517302898751245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77034278273011535265834163 115551417409517302898751245)
      ·
        refine ⟨43331781528568988587031717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 115551417409517302898751245 43331781528568988587031717)
        ·
          refine ⟨8124709036606685360068447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43331781528568988587031717 8124709036606685360068447)
          ·
            refine ⟨12187063554910028040102671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8124709036606685360068447 12187063554910028040102671)
            ·
              refine ⟨18280595332365042060154007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12187063554910028040102671 18280595332365042060154007)
              ·
                refine ⟨27420892998547563090231011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18280595332365042060154007 27420892998547563090231011)
                ·
                  refine ⟨41131339497821344635346517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27420892998547563090231011 41131339497821344635346517)
                  ·
                    refine ⟨482007884740093882445467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 41131339497821344635346517 482007884740093882445467)
                    ·
                      rfl

theorem cell23_2816121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 1, 1, 8].length) (baseStart_2816121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2816121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2816121 prefixEnd_2816121 := by exact prefixLift 2816121
  have htrace : WordTrace (prefixWord ++ tailWord_2816121) baseStart_2816121 baseEnd_2816121 := by
    simpa [prefixWord, tailWord_2816121, baseEnd_2816121] using wordTrace_append hprefix tailTrace_2816121
  have hstable : (prefixWord ++ tailWord_2816121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2816121).length < 2 ^ (prefixWord ++ tailWord_2816121).sum := by decide
  have hdescent : baseEnd_2816121 < baseStart_2816121 := by decide
  rcases family_descends (prefixWord ++ tailWord_2816121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2816150 : List Nat := [5, 3, 2, 1, 2, 1, 1, 2, 2, 4]
def baseStart_2816150 : Nat := 118140960795 + 2816150 * 2 ^ 59
def prefixEnd_2816150 : Nat := 4983230072969 + 3 ^ 40 * 2816150 * 2
def baseEnd_2816150 : Nat := 482012848386420677957923

theorem tailTrace_2816150 : CollatzResearch.WordTrace tailWord_2816150 prefixEnd_2816150 482012848386420677957923 := by
  unfold tailWord_2816150
  simp only [CollatzResearch.WordTrace]
  refine ⟨6419589296723561560869869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 68475619165051323315945269 6419589296723561560869869)
  ·
    refine ⟨2407345986271335585326201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6419589296723561560869869 2407345986271335585326201)
    ·
      refine ⟨1805509489703501688994651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2407345986271335585326201 1805509489703501688994651)
      ·
        refine ⟨2708264234555252533491977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1805509489703501688994651 2708264234555252533491977)
        ·
          refine ⟨2031198175916439400118983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2708264234555252533491977 2031198175916439400118983)
          ·
            refine ⟨3046797263874659100178475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2031198175916439400118983 3046797263874659100178475)
            ·
              refine ⟨4570195895811988650267713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3046797263874659100178475 4570195895811988650267713)
              ·
                refine ⟨3427646921858991487700785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4570195895811988650267713 3427646921858991487700785)
                ·
                  refine ⟨2570735191394243615775589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3427646921858991487700785 2570735191394243615775589)
                  ·
                    refine ⟨482012848386420677957923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2570735191394243615775589 482012848386420677957923)
                    ·
                      rfl

theorem cell23_2816150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 1, 2, 2, 4].length) (baseStart_2816150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2816150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2816150 prefixEnd_2816150 := by exact prefixLift 2816150
  have htrace : WordTrace (prefixWord ++ tailWord_2816150) baseStart_2816150 baseEnd_2816150 := by
    simpa [prefixWord, tailWord_2816150, baseEnd_2816150] using wordTrace_append hprefix tailTrace_2816150
  have hstable : (prefixWord ++ tailWord_2816150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2816150).length < 2 ^ (prefixWord ++ tailWord_2816150).sum := by decide
  have hdescent : baseEnd_2816150 < baseStart_2816150 := by decide
  rcases family_descends (prefixWord ++ tailWord_2816150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2816178 : List Nat := [3, 2, 1, 1, 1, 3, 1, 3, 2, 3, 3]
def baseStart_2816178 : Nat := 118140960795 + 2816178 * 2 ^ 59
def prefixEnd_2816178 : Nat := 4983230072969 + 3 ^ 40 * 2816178 * 2
def baseEnd_2816178 : Nat := 1446052922617587924323639

theorem tailTrace_2816178 : CollatzResearch.WordTrace tailWord_2816178 prefixEnd_2816178 1446052922617587924323639 := by
  unfold tailWord_2816178
  simp only [CollatzResearch.WordTrace]
  refine ⟨25678612497868886438984297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68476299994317030503958125 25678612497868886438984297)
  ·
    refine ⟨19258959373401664829238223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25678612497868886438984297 19258959373401664829238223)
    ·
      refine ⟨28888439060102497243857335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19258959373401664829238223 28888439060102497243857335)
      ·
        refine ⟨43332658590153745865786003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28888439060102497243857335 43332658590153745865786003)
        ·
          refine ⟨64998987885230618798679005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43332658590153745865786003 64998987885230618798679005)
          ·
            refine ⟨24374620456961482049504627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64998987885230618798679005 24374620456961482049504627)
            ·
              refine ⟨36561930685442223074256941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24374620456961482049504627 36561930685442223074256941)
              ·
                refine ⟨13710724007040833652846353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36561930685442223074256941 13710724007040833652846353)
                ·
                  refine ⟨10283043005280625239634765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13710724007040833652846353 10283043005280625239634765)
                  ·
                    refine ⟨3856141126980234464863037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10283043005280625239634765 3856141126980234464863037)
                    ·
                      refine ⟨1446052922617587924323639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3856141126980234464863037 1446052922617587924323639)
                      ·
                        rfl

theorem cell23_2816178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 3, 2, 3, 3].length) (baseStart_2816178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2816178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2816178 prefixEnd_2816178 := by exact prefixLift 2816178
  have htrace : WordTrace (prefixWord ++ tailWord_2816178) baseStart_2816178 baseEnd_2816178 := by
    simpa [prefixWord, tailWord_2816178, baseEnd_2816178] using wordTrace_append hprefix tailTrace_2816178
  have hstable : (prefixWord ++ tailWord_2816178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2816178).length < 2 ^ (prefixWord ++ tailWord_2816178).sum := by decide
  have hdescent : baseEnd_2816178 < baseStart_2816178 := by decide
  rcases family_descends (prefixWord ++ tailWord_2816178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2816191 : List Nat := [1, 1, 2, 2, 2, 2, 1, 2, 3, 2, 5]
def baseStart_2816191 : Nat := 118140960795 + 2816191 * 2 ^ 59
def prefixEnd_2816191 : Nat := 4983230072969 + 3 ^ 40 * 2816191 * 2
def baseEnd_2816191 : Nat := 1446059597866096373461079

theorem tailTrace_2816191 : CollatzResearch.WordTrace tailWord_2816191 prefixEnd_2816191 1446059597866096373461079 := by
  unfold tailWord_2816191
  simp only [CollatzResearch.WordTrace]
  refine ⟨102714924140428448976160427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68476616093618965984106951 102714924140428448976160427)
  ·
    refine ⟨154072386210642673464240641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102714924140428448976160427 154072386210642673464240641)
    ·
      refine ⟨115554289657982005098180481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154072386210642673464240641 115554289657982005098180481)
      ·
        refine ⟨86665717243486503823635361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115554289657982005098180481 86665717243486503823635361)
        ·
          refine ⟨64999287932614877867726521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86665717243486503823635361 64999287932614877867726521)
          ·
            refine ⟨48749465949461158400794891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64999287932614877867726521 48749465949461158400794891)
            ·
              refine ⟨73124198924191737601192337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48749465949461158400794891 73124198924191737601192337)
              ·
                refine ⟨54843149193143803200894253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73124198924191737601192337 54843149193143803200894253)
                ·
                  refine ⟨20566180947428926200335345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54843149193143803200894253 20566180947428926200335345)
                  ·
                    refine ⟨15424635710571694650251509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20566180947428926200335345 15424635710571694650251509)
                    ·
                      refine ⟨1446059597866096373461079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15424635710571694650251509 1446059597866096373461079)
                      ·
                        rfl

theorem cell23_2816191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 2, 3, 2, 5].length) (baseStart_2816191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2816191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2816191 prefixEnd_2816191 := by exact prefixLift 2816191
  have htrace : WordTrace (prefixWord ++ tailWord_2816191) baseStart_2816191 baseEnd_2816191 := by
    simpa [prefixWord, tailWord_2816191, baseEnd_2816191] using wordTrace_append hprefix tailTrace_2816191
  have hstable : (prefixWord ++ tailWord_2816191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2816191).length < 2 ^ (prefixWord ++ tailWord_2816191).sum := by decide
  have hdescent : baseEnd_2816191 < baseStart_2816191 := by decide
  rcases family_descends (prefixWord ++ tailWord_2816191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2816218 : List Nat := [3, 1, 1, 2, 2, 1, 3, 1, 4, 1, 4]
def baseStart_2816218 : Nat := 118140960795 + 2816218 * 2 ^ 59
def prefixEnd_2816218 : Nat := 4983230072969 + 3 ^ 40 * 2816218 * 2
def baseEnd_2816218 : Nat := 1446073461843767767823455

theorem tailTrace_2816218 : CollatzResearch.WordTrace tailWord_2816218 prefixEnd_2816218 1446073461843767767823455 := by
  unfold tailWord_2816218
  simp only [CollatzResearch.WordTrace]
  refine ⟨25678977227832658146848327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68477272607553755058262205 25678977227832658146848327)
  ·
    refine ⟨38518465841748987220272491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25678977227832658146848327 38518465841748987220272491)
    ·
      refine ⟨57777698762623480830408737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38518465841748987220272491 57777698762623480830408737)
      ·
        refine ⟨43333274071967610622806553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57777698762623480830408737 43333274071967610622806553)
        ·
          refine ⟨32499955553975707967104915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43333274071967610622806553 32499955553975707967104915)
          ·
            refine ⟨48749933330963561950657373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32499955553975707967104915 48749933330963561950657373)
            ·
              refine ⟨18281224999111335731496515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48749933330963561950657373 18281224999111335731496515)
              ·
                refine ⟨27421837498667003597244773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18281224999111335731496515 27421837498667003597244773)
                ·
                  refine ⟨5141594531000063174483395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27421837498667003597244773 5141594531000063174483395)
                  ·
                    refine ⟨7712391796500094761725093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5141594531000063174483395 7712391796500094761725093)
                    ·
                      refine ⟨1446073461843767767823455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7712391796500094761725093 1446073461843767767823455)
                      ·
                        rfl

theorem cell23_2816218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 1, 4, 1, 4].length) (baseStart_2816218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2816218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2816218 prefixEnd_2816218 := by exact prefixLift 2816218
  have htrace : WordTrace (prefixWord ++ tailWord_2816218) baseStart_2816218 baseEnd_2816218 := by
    simpa [prefixWord, tailWord_2816218, baseEnd_2816218] using wordTrace_append hprefix tailTrace_2816218
  have hstable : (prefixWord ++ tailWord_2816218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2816218).length < 2 ^ (prefixWord ++ tailWord_2816218).sum := by decide
  have hdescent : baseEnd_2816218 < baseStart_2816218 := by decide
  rcases family_descends (prefixWord ++ tailWord_2816218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2816255 : List Nat := [1, 1, 2, 2, 1, 4, 4, 1, 2, 2, 3]
def baseStart_2816255 : Nat := 118140960795 + 2816255 * 2 ^ 59
def prefixEnd_2816255 : Nat := 4983230072969 + 3 ^ 40 * 2816255 * 2
def baseEnd_2816255 : Nat := 1446092460627984123060785

theorem tailTrace_2816255 : CollatzResearch.WordTrace tailWord_2816255 prefixEnd_2816255 1446092460627984123060785 := by
  unfold tailWord_2816255
  simp only [CollatzResearch.WordTrace]
  refine ⟨102717258412196587906490219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68478172274797725270993479 102717258412196587906490219)
  ·
    refine ⟨154075887618294881859735329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102717258412196587906490219 154075887618294881859735329)
    ·
      refine ⟨115556915713721161394801497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154075887618294881859735329 115556915713721161394801497)
      ·
        refine ⟨86667686785290871046101123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115556915713721161394801497 86667686785290871046101123)
        ·
          refine ⟨130001530177936306569151685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86667686785290871046101123 130001530177936306569151685)
          ·
            refine ⟨24375286908363057481715941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 130001530177936306569151685 24375286908363057481715941)
            ·
              refine ⟨4570366295318073277821739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24375286908363057481715941 4570366295318073277821739)
              ·
                refine ⟨6855549442977109916732609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4570366295318073277821739 6855549442977109916732609)
                ·
                  refine ⟨5141662082232832437549457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6855549442977109916732609 5141662082232832437549457)
                  ·
                    refine ⟨3856246561674624328162093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5141662082232832437549457 3856246561674624328162093)
                    ·
                      refine ⟨1446092460627984123060785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3856246561674624328162093 1446092460627984123060785)
                      ·
                        rfl

theorem cell23_2816255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 4, 1, 2, 2, 3].length) (baseStart_2816255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2816255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2816255 prefixEnd_2816255 := by exact prefixLift 2816255
  have htrace : WordTrace (prefixWord ++ tailWord_2816255) baseStart_2816255 baseEnd_2816255 := by
    simpa [prefixWord, tailWord_2816255, baseEnd_2816255] using wordTrace_append hprefix tailTrace_2816255
  have hstable : (prefixWord ++ tailWord_2816255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2816255).length < 2 ^ (prefixWord ++ tailWord_2816255).sum := by decide
  have hdescent : baseEnd_2816255 < baseStart_2816255 := by decide
  rcases family_descends (prefixWord ++ tailWord_2816255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2816279 : List Nat := [1, 1, 3, 4, 1, 2, 4, 2, 1, 4]
def baseStart_2816279 : Nat := 118140960795 + 2816279 * 2 ^ 59
def prefixEnd_2816279 : Nat := 4983230072969 + 3 ^ 40 * 2816279 * 2
def baseEnd_2816279 : Nat := 482034928054564009720225

theorem tailTrace_2816279 : CollatzResearch.WordTrace tailWord_2816279 prefixEnd_2816279 482034928054564009720225 := by
  unfold tailWord_2816279
  simp only [CollatzResearch.WordTrace]
  refine ⟨102718133764109640005363891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68478755842739760003575927 102718133764109640005363891)
  ·
    refine ⟨154077200646164460008045837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102718133764109640005363891 154077200646164460008045837)
    ·
      refine ⟨57778950242311672503017189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 154077200646164460008045837 57778950242311672503017189)
      ·
        refine ⟨10833553170433438594315723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57778950242311672503017189 10833553170433438594315723)
        ·
          refine ⟨16250329755650157891473585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10833553170433438594315723 16250329755650157891473585)
          ·
            refine ⟨12187747316737618418605189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16250329755650157891473585 12187747316737618418605189)
            ·
              refine ⟨2285202621888303453488473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12187747316737618418605189 2285202621888303453488473)
              ·
                refine ⟨1713901966416227590116355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2285202621888303453488473 1713901966416227590116355)
                ·
                  refine ⟨2570852949624341385174533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1713901966416227590116355 2570852949624341385174533)
                  ·
                    refine ⟨482034928054564009720225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2570852949624341385174533 482034928054564009720225)
                    ·
                      rfl

theorem cell23_2816279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 4, 2, 1, 4].length) (baseStart_2816279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2816279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2816279 prefixEnd_2816279 := by exact prefixLift 2816279
  have htrace : WordTrace (prefixWord ++ tailWord_2816279) baseStart_2816279 baseEnd_2816279 := by
    simpa [prefixWord, tailWord_2816279, baseEnd_2816279] using wordTrace_append hprefix tailTrace_2816279
  have hstable : (prefixWord ++ tailWord_2816279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2816279).length < 2 ^ (prefixWord ++ tailWord_2816279).sum := by decide
  have hdescent : baseEnd_2816279 < baseStart_2816279 := by decide
  rcases family_descends (prefixWord ++ tailWord_2816279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2816312 : List Nat := [2, 1, 2, 1, 3, 1, 5, 1, 2, 3, 2]
def baseStart_2816312 : Nat := 118140960795 + 2816312 * 2 ^ 59
def prefixEnd_2816312 : Nat := 4983230072969 + 3 ^ 40 * 2816312 * 2
def baseEnd_2816312 : Nat := 1446121729025290400048023

theorem tailTrace_2816312 : CollatzResearch.WordTrace tailWord_2816312 prefixEnd_2816312 1446121729025290400048023 := by
  unfold tailWord_2816312
  simp only [CollatzResearch.WordTrace]
  refine ⟨51359668686495043320657595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68479558248660057760876793 51359668686495043320657595)
  ·
    refine ⟨77039503029742564980986393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51359668686495043320657595 77039503029742564980986393)
    ·
      refine ⟨57779627272306923735739795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77039503029742564980986393 57779627272306923735739795)
      ·
        refine ⟨86669440908460385603609693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57779627272306923735739795 86669440908460385603609693)
        ·
          refine ⟨32501040340672644601353635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86669440908460385603609693 32501040340672644601353635)
          ·
            refine ⟨48751560511008966902030453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32501040340672644601353635 48751560511008966902030453)
            ·
              refine ⟨4570458797907090647065355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 48751560511008966902030453 4570458797907090647065355)
              ·
                refine ⟨6855688196860635970598033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4570458797907090647065355 6855688196860635970598033)
                ·
                  refine ⟨5141766147645476977948525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6855688196860635970598033 5141766147645476977948525)
                  ·
                    refine ⟨1928162305367053866730697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5141766147645476977948525 1928162305367053866730697)
                    ·
                      refine ⟨1446121729025290400048023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1928162305367053866730697 1446121729025290400048023)
                      ·
                        rfl

theorem cell23_2816312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 5, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 5, 1, 2, 3, 2].length) (baseStart_2816312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2816312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2816312 prefixEnd_2816312 := by exact prefixLift 2816312
  have htrace : WordTrace (prefixWord ++ tailWord_2816312) baseStart_2816312 baseEnd_2816312 := by
    simpa [prefixWord, tailWord_2816312, baseEnd_2816312] using wordTrace_append hprefix tailTrace_2816312
  have hstable : (prefixWord ++ tailWord_2816312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2816312).length < 2 ^ (prefixWord ++ tailWord_2816312).sum := by decide
  have hdescent : baseEnd_2816312 < baseStart_2816312 := by decide
  rcases family_descends (prefixWord ++ tailWord_2816312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2816319 : List Nat := [1, 1, 2, 2, 4, 1, 4, 3, 1, 1, 3]
def baseStart_2816319 : Nat := 118140960795 + 2816319 * 2 ^ 59
def prefixEnd_2816319 : Nat := 4983230072969 + 3 ^ 40 * 2816319 * 2
def baseEnd_2816319 : Nat := 1446125323389871872660491

theorem tailTrace_2816319 : CollatzResearch.WordTrace tailWord_2816319 prefixEnd_2816319 1446125323389871872660491 := by
  unfold tailWord_2816319
  simp only [CollatzResearch.WordTrace]
  refine ⟨102719592683964726836820011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68479728455976484557880007 102719592683964726836820011)
  ·
    refine ⟨154079389025947090255230017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102719592683964726836820011 154079389025947090255230017)
    ·
      refine ⟨115559541769460317691422513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154079389025947090255230017 115559541769460317691422513)
      ·
        refine ⟨86669656327095238268566885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115559541769460317691422513 86669656327095238268566885)
        ·
          refine ⟨16250560561330357175356291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 86669656327095238268566885 16250560561330357175356291)
          ·
            refine ⟨24375840841995535763034437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16250560561330357175356291 24375840841995535763034437)
            ·
              refine ⟨4570470157874162955568957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24375840841995535763034437 4570470157874162955568957)
              ·
                refine ⟨1713926309202811108338359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4570470157874162955568957 1713926309202811108338359)
                ·
                  refine ⟨2570889463804216662507539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1713926309202811108338359 2570889463804216662507539)
                  ·
                    refine ⟨3856334195706324993761309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2570889463804216662507539 3856334195706324993761309)
                    ·
                      refine ⟨1446125323389871872660491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3856334195706324993761309 1446125323389871872660491)
                      ·
                        rfl

theorem cell23_2816319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 4, 3, 1, 1, 3].length) (baseStart_2816319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2816319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2816319 prefixEnd_2816319 := by exact prefixLift 2816319
  have htrace : WordTrace (prefixWord ++ tailWord_2816319) baseStart_2816319 baseEnd_2816319 := by
    simpa [prefixWord, tailWord_2816319, baseEnd_2816319] using wordTrace_append hprefix tailTrace_2816319
  have hstable : (prefixWord ++ tailWord_2816319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2816319).length < 2 ^ (prefixWord ++ tailWord_2816319).sum := by decide
  have hdescent : baseEnd_2816319 < baseStart_2816319 := by decide
  rcases family_descends (prefixWord ++ tailWord_2816319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2816335 : List Nat := [1, 1, 2, 1, 1, 2, 1, 8, 2, 4]
def baseStart_2816335 : Nat := 118140960795 + 2816335 * 2 ^ 59
def prefixEnd_2816335 : Nat := 4983230072969 + 3 ^ 40 * 2816335 * 2
def baseEnd_2816335 : Nat := 482044513026781270020139

theorem tailTrace_2816335 : CollatzResearch.WordTrace tailWord_2816335 prefixEnd_2816335 482044513026781270020139 := by
  unfold tailWord_2816335
  simp only [CollatzResearch.WordTrace]
  refine ⟨102720176251906761569402459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68480117501271174379601639 102720176251906761569402459)
  ·
    refine ⟨154080264377860142354103689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102720176251906761569402459 154080264377860142354103689)
    ·
      refine ⟨115560198283395106765577767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154080264377860142354103689 115560198283395106765577767)
      ·
        refine ⟨173340297425092660148366651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115560198283395106765577767 173340297425092660148366651)
        ·
          refine ⟨260010446137638990222549977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173340297425092660148366651 260010446137638990222549977)
          ·
            refine ⟨195007834603229242666912483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 260010446137638990222549977 195007834603229242666912483)
            ·
              refine ⟨292511751904843864000368725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 195007834603229242666912483 292511751904843864000368725)
              ·
                refine ⟨3427872092634889031254321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 292511751904843864000368725 3427872092634889031254321)
                ·
                  refine ⟨2570904069476166773440741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3427872092634889031254321 2570904069476166773440741)
                  ·
                    refine ⟨482044513026781270020139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2570904069476166773440741 482044513026781270020139)
                    ·
                      rfl

theorem cell23_2816335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 8, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 8, 2, 4].length) (baseStart_2816335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2816335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2816335 prefixEnd_2816335 := by exact prefixLift 2816335
  have htrace : WordTrace (prefixWord ++ tailWord_2816335) baseStart_2816335 baseEnd_2816335 := by
    simpa [prefixWord, tailWord_2816335, baseEnd_2816335] using wordTrace_append hprefix tailTrace_2816335
  have hstable : (prefixWord ++ tailWord_2816335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2816335).length < 2 ^ (prefixWord ++ tailWord_2816335).sum := by decide
  have hdescent : baseEnd_2816335 < baseStart_2816335 := by decide
  rcases family_descends (prefixWord ++ tailWord_2816335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2816352 : List Nat := [2, 1, 1, 3, 5, 2, 1, 1, 1, 6]
def baseStart_2816352 : Nat := 118140960795 + 2816352 * 2 ^ 59
def prefixEnd_2816352 : Nat := 4983230072969 + 3 ^ 40 * 2816352 * 2
def baseEnd_2816352 : Nat := 482047422750490081182613

theorem tailTrace_2816352 : CollatzResearch.WordTrace tailWord_2816352 prefixEnd_2816352 482047422750490081182613 := by
  unfold tailWord_2816352
  simp only [CollatzResearch.WordTrace]
  refine ⟨51360398146422586736385655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68480530861896782315180873 51360398146422586736385655)
  ·
    refine ⟨77040597219633880104578483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51360398146422586736385655 77040597219633880104578483)
    ·
      refine ⟨115560895829450820156867725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77040597219633880104578483 115560895829450820156867725)
      ·
        refine ⟨43335335936044057558825397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 115560895829450820156867725 43335335936044057558825397)
        ·
          refine ⟨4062687744004130396139881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 43335335936044057558825397 4062687744004130396139881)
          ·
            refine ⟨3047015808003097797104911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4062687744004130396139881 3047015808003097797104911)
            ·
              refine ⟨4570523712004646695657367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3047015808003097797104911 4570523712004646695657367)
              ·
                refine ⟨6855785568006970043486051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4570523712004646695657367 6855785568006970043486051)
                ·
                  refine ⟨10283678352010455065229077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6855785568006970043486051 10283678352010455065229077)
                  ·
                    refine ⟨482047422750490081182613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10283678352010455065229077 482047422750490081182613)
                    ·
                      rfl

theorem cell23_2816352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 1, 1, 1, 6].length) (baseStart_2816352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2816352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2816352 prefixEnd_2816352 := by exact prefixLift 2816352
  have htrace : WordTrace (prefixWord ++ tailWord_2816352) baseStart_2816352 baseEnd_2816352 := by
    simpa [prefixWord, tailWord_2816352, baseEnd_2816352] using wordTrace_append hprefix tailTrace_2816352
  have hstable : (prefixWord ++ tailWord_2816352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2816352).length < 2 ^ (prefixWord ++ tailWord_2816352).sum := by decide
  have hdescent : baseEnd_2816352 < baseStart_2816352 := by decide
  rcases family_descends (prefixWord ++ tailWord_2816352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2816359 : List Nat := [1, 1, 5, 1, 3, 1, 2, 2, 3, 2, 2]
def baseStart_2816359 : Nat := 118140960795 + 2816359 * 2 ^ 59
def prefixEnd_2816359 : Nat := 4983230072969 + 3 ^ 40 * 2816359 * 2
def baseEnd_2816359 : Nat := 1446145862616051716160307

theorem tailTrace_2816359 : CollatzResearch.WordTrace tailWord_2816359 prefixEnd_2816359 1446145862616051716160307 := by
  unfold tailWord_2816359
  simp only [CollatzResearch.WordTrace]
  refine ⟨102721051603819813668276131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68480701069213209112184087 102721051603819813668276131)
  ·
    refine ⟨154081577405729720502414197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102721051603819813668276131 154081577405729720502414197)
    ·
      refine ⟨14445147881787161297101331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 154081577405729720502414197 14445147881787161297101331)
      ·
        refine ⟨21667721822680741945651997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14445147881787161297101331 21667721822680741945651997)
        ·
          refine ⟨8125395683505278229619499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21667721822680741945651997 8125395683505278229619499)
          ·
            refine ⟨12188093525257917344429249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8125395683505278229619499 12188093525257917344429249)
            ·
              refine ⟨9141070143943438008321937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12188093525257917344429249 9141070143943438008321937)
              ·
                refine ⟨6855802607957578506241453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9141070143943438008321937 6855802607957578506241453)
                ·
                  refine ⟨2570925977984091939840545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6855802607957578506241453 2570925977984091939840545)
                  ·
                    refine ⟨1928194483488068954880409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2570925977984091939840545 1928194483488068954880409)
                    ·
                      refine ⟨1446145862616051716160307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1928194483488068954880409 1446145862616051716160307)
                      ·
                        rfl

theorem cell23_2816359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 2, 2, 3, 2, 2].length) (baseStart_2816359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2816359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2816359 prefixEnd_2816359 := by exact prefixLift 2816359
  have htrace : WordTrace (prefixWord ++ tailWord_2816359) baseStart_2816359 baseEnd_2816359 := by
    simpa [prefixWord, tailWord_2816359, baseEnd_2816359] using wordTrace_append hprefix tailTrace_2816359
  have hstable : (prefixWord ++ tailWord_2816359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2816359).length < 2 ^ (prefixWord ++ tailWord_2816359).sum := by decide
  have hdescent : baseEnd_2816359 < baseStart_2816359 := by decide
  rcases family_descends (prefixWord ++ tailWord_2816359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2816392 : List Nat := [2, 1, 3, 3, 1, 1, 1, 3, 4, 1, 3]
def baseStart_2816392 : Nat := 118140960795 + 2816392 * 2 ^ 59
def prefixEnd_2816392 : Nat := 4983230072969 + 3 ^ 40 * 2816392 * 2
def baseEnd_2816392 : Nat := 1446162807477650087047655

theorem tailTrace_2816392 : CollatzResearch.WordTrace tailWord_2816392 prefixEnd_2816392 1446162807477650087047655 := by
  unfold tailWord_2816392
  simp only [CollatzResearch.WordTrace]
  refine ⟨51361127606350130152113715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68481503475133506869484953 51361127606350130152113715)
  ·
    refine ⟨77041691409525195228170573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51361127606350130152113715 77041691409525195228170573)
    ·
      refine ⟨28890634278571948210563965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77041691409525195228170573 28890634278571948210563965)
      ·
        refine ⟨10833987854464480578961487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28890634278571948210563965 10833987854464480578961487)
        ·
          refine ⟨16250981781696720868442231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10833987854464480578961487 16250981781696720868442231)
          ·
            refine ⟨24376472672545081302663347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16250981781696720868442231 24376472672545081302663347)
            ·
              refine ⟨36564709008817621953995021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24376472672545081302663347 36564709008817621953995021)
              ·
                refine ⟨13711765878306608232748133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36564709008817621953995021 13711765878306608232748133)
                ·
                  refine ⟨2570956102182489043640275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13711765878306608232748133 2570956102182489043640275)
                  ·
                    refine ⟨3856434153273733565460413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2570956102182489043640275 3856434153273733565460413)
                    ·
                      refine ⟨1446162807477650087047655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3856434153273733565460413 1446162807477650087047655)
                      ·
                        rfl

theorem cell23_2816392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 3, 4, 1, 3].length) (baseStart_2816392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2816392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2816392 prefixEnd_2816392 := by exact prefixLift 2816392
  have htrace : WordTrace (prefixWord ++ tailWord_2816392) baseStart_2816392 baseEnd_2816392 := by
    simpa [prefixWord, tailWord_2816392, baseEnd_2816392] using wordTrace_append hprefix tailTrace_2816392
  have hstable : (prefixWord ++ tailWord_2816392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2816392).length < 2 ^ (prefixWord ++ tailWord_2816392).sum := by decide
  have hdescent : baseEnd_2816392 < baseStart_2816392 := by decide
  rcases family_descends (prefixWord ++ tailWord_2816392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2816393 : List Nat := [1, 2, 1, 1, 6, 2, 3, 2, 1, 2, 2]
def baseStart_2816393 : Nat := 118140960795 + 2816393 * 2 ^ 59
def prefixEnd_2816393 : Nat := 4983230072969 + 3 ^ 40 * 2816393 * 2
def baseEnd_2816393 : Nat := 1446163320958304583135151

theorem tailTrace_2816393 : CollatzResearch.WordTrace tailWord_2816393 prefixEnd_2816393 1446163320958304583135151 := by
  unfold tailWord_2816393
  simp only [CollatzResearch.WordTrace]
  refine ⟨102722291685696637475013833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68481527790464424983342555 102722291685696637475013833)
  ·
    refine ⟨77041718764272478106260375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102722291685696637475013833 77041718764272478106260375)
    ·
      refine ⟨115562578146408717159390563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77041718764272478106260375 115562578146408717159390563)
      ·
        refine ⟨173343867219613075739085845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115562578146408717159390563 173343867219613075739085845)
        ·
          refine ⟨8125493775919362925269649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 173343867219613075739085845 8125493775919362925269649)
          ·
            refine ⟨6094120331939522193952237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8125493775919362925269649 6094120331939522193952237)
            ·
              refine ⟨2285295124477320822732089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6094120331939522193952237 2285295124477320822732089)
              ·
                refine ⟨1713971343357990617049067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2285295124477320822732089 1713971343357990617049067)
                ·
                  refine ⟨2570957015036985925573601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1713971343357990617049067 2570957015036985925573601)
                  ·
                    refine ⟨1928217761277739444180201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2570957015036985925573601 1928217761277739444180201)
                    ·
                      refine ⟨1446163320958304583135151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1928217761277739444180201 1446163320958304583135151)
                      ·
                        rfl

theorem cell23_2816393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 3, 2, 1, 2, 2].length) (baseStart_2816393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2816393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2816393 prefixEnd_2816393 := by exact prefixLift 2816393
  have htrace : WordTrace (prefixWord ++ tailWord_2816393) baseStart_2816393 baseEnd_2816393 := by
    simpa [prefixWord, tailWord_2816393, baseEnd_2816393] using wordTrace_append hprefix tailTrace_2816393
  have hstable : (prefixWord ++ tailWord_2816393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2816393).length < 2 ^ (prefixWord ++ tailWord_2816393).sum := by decide
  have hdescent : baseEnd_2816393 < baseStart_2816393 := by decide
  rcases family_descends (prefixWord ++ tailWord_2816393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2816419 : List Nat := [1, 1, 1, 4, 1, 4, 3, 2, 1, 3, 2]
def baseStart_2816419 : Nat := 118140960795 + 2816419 * 2 ^ 59
def prefixEnd_2816419 : Nat := 4983230072969 + 3 ^ 40 * 2816419 * 2
def baseEnd_2816419 : Nat := 1446176671455321481410031

theorem tailTrace_2816419 : CollatzResearch.WordTrace tailWord_2816419 prefixEnd_2816419 1446176671455321481410031 := by
  unfold tailWord_2816419
  simp only [CollatzResearch.WordTrace]
  refine ⟨102723239983602443915460311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68482159989068295943640207 102723239983602443915460311)
  ·
    refine ⟨154084859975403665873190467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102723239983602443915460311 154084859975403665873190467)
    ·
      refine ⟨231127289963105498809785701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154084859975403665873190467 231127289963105498809785701)
      ·
        refine ⟨43336366868082281026834819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 231127289963105498809785701 43336366868082281026834819)
        ·
          refine ⟨65004550302123421540252229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43336366868082281026834819 65004550302123421540252229)
          ·
            refine ⟨12188353181648141538797293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 65004550302123421540252229 12188353181648141538797293)
            ·
              refine ⟨4570632443118053077048985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12188353181648141538797293 4570632443118053077048985)
              ·
                refine ⟨3427974332338539807786739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4570632443118053077048985 3427974332338539807786739)
                ·
                  refine ⟨5141961498507809711680109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3427974332338539807786739 5141961498507809711680109)
                  ·
                    refine ⟨1928235561940428641880041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5141961498507809711680109 1928235561940428641880041)
                    ·
                      refine ⟨1446176671455321481410031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1928235561940428641880041 1446176671455321481410031)
                      ·
                        rfl

theorem cell23_2816419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 3, 2, 1, 3, 2].length) (baseStart_2816419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2816419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2816419 prefixEnd_2816419 := by exact prefixLift 2816419
  have htrace : WordTrace (prefixWord ++ tailWord_2816419) baseStart_2816419 baseEnd_2816419 := by
    simpa [prefixWord, tailWord_2816419, baseEnd_2816419] using wordTrace_append hprefix tailTrace_2816419
  have hstable : (prefixWord ++ tailWord_2816419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2816419).length < 2 ^ (prefixWord ++ tailWord_2816419).sum := by decide
  have hdescent : baseEnd_2816419 < baseStart_2816419 := by decide
  rcases family_descends (prefixWord ++ tailWord_2816419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2816502 : List Nat := [5, 1, 1, 1, 2, 1, 2, 1, 4, 5]
def baseStart_2816502 : Nat := 118140960795 + 2816502 * 2 ^ 59
def prefixEnd_2816502 : Nat := 4983230072969 + 3 ^ 40 * 2816502 * 2
def baseEnd_2816502 : Nat := 482073096783214885557383

theorem tailTrace_2816502 : CollatzResearch.WordTrace tailWord_2816502 prefixEnd_2816502 482073096783214885557383 := by
  unfold tailWord_2816502
  simp only [CollatzResearch.WordTrace]
  refine ⟨6420391702643859318170735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 68484178161534499393821173 6420391702643859318170735)
  ·
    refine ⟨9630587553965788977256103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6420391702643859318170735 9630587553965788977256103)
    ·
      refine ⟨14445881330948683465884155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9630587553965788977256103 14445881330948683465884155)
      ·
        refine ⟨21668821996423025198826233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14445881330948683465884155 21668821996423025198826233)
        ·
          refine ⟨16251616497317268899119675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21668821996423025198826233 16251616497317268899119675)
          ·
            refine ⟨24377424745975903348679513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16251616497317268899119675 24377424745975903348679513)
            ·
              refine ⟨18283068559481927511509635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24377424745975903348679513 18283068559481927511509635)
              ·
                refine ⟨27424602839222891267264453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18283068559481927511509635 27424602839222891267264453)
                ·
                  refine ⟨5142113032354292112612085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27424602839222891267264453 5142113032354292112612085)
                  ·
                    refine ⟨482073096783214885557383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5142113032354292112612085 482073096783214885557383)
                    ·
                      rfl

theorem cell23_2816502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 1, 4, 5].length) (baseStart_2816502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2816502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2816502 prefixEnd_2816502 := by exact prefixLift 2816502
  have htrace : WordTrace (prefixWord ++ tailWord_2816502) baseStart_2816502 baseEnd_2816502 := by
    simpa [prefixWord, tailWord_2816502, baseEnd_2816502] using wordTrace_append hprefix tailTrace_2816502
  have hstable : (prefixWord ++ tailWord_2816502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2816502).length < 2 ^ (prefixWord ++ tailWord_2816502).sum := by decide
  have hdescent : baseEnd_2816502 < baseStart_2816502 := by decide
  rcases family_descends (prefixWord ++ tailWord_2816502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2816545 : List Nat := [1, 2, 3, 2, 2, 1, 1, 1, 10]
def baseStart_2816545 : Nat := 118140960795 + 2816545 * 2 ^ 59
def prefixEnd_2816545 : Nat := 4983230072969 + 3 ^ 40 * 2816545 * 2
def baseEnd_2816545 : Nat := 160693485557531998714939

theorem tailTrace_2816545 : CollatzResearch.WordTrace tailWord_2816545 prefixEnd_2816545 160693485557531998714939 := by
  unfold tailWord_2816545
  simp only [CollatzResearch.WordTrace]
  refine ⟨102727835581145967434547089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68485223720763978289698059 102727835581145967434547089)
  ·
    refine ⟨77045876685859475575910317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102727835581145967434547089 77045876685859475575910317)
    ·
      refine ⟨28892203757197303340966369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77045876685859475575910317 28892203757197303340966369)
      ·
        refine ⟨21669152817897977505724777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28892203757197303340966369 21669152817897977505724777)
        ·
          refine ⟨16251864613423483129293583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21669152817897977505724777 16251864613423483129293583)
          ·
            refine ⟨24377796920135224693940375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16251864613423483129293583 24377796920135224693940375)
            ·
              refine ⟨36566695380202837040910563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24377796920135224693940375 36566695380202837040910563)
              ·
                refine ⟨54850043070304255561365845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36566695380202837040910563 54850043070304255561365845)
                ·
                  refine ⟨160693485557531998714939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 54850043070304255561365845 160693485557531998714939)
                  ·
                    rfl

theorem cell23_2816545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 1, 10].length) (baseStart_2816545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2816545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2816545 prefixEnd_2816545 := by exact prefixLift 2816545
  have htrace : WordTrace (prefixWord ++ tailWord_2816545) baseStart_2816545 baseEnd_2816545 := by
    simpa [prefixWord, tailWord_2816545, baseEnd_2816545] using wordTrace_append hprefix tailTrace_2816545
  have hstable : (prefixWord ++ tailWord_2816545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2816545).length < 2 ^ (prefixWord ++ tailWord_2816545).sum := by decide
  have hdescent : baseEnd_2816545 < baseStart_2816545 := by decide
  rcases family_descends (prefixWord ++ tailWord_2816545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2816566 : List Nat := [5, 1, 2, 1, 2, 1, 3, 1, 3, 4]
def baseStart_2816566 : Nat := 118140960795 + 2816566 * 2 ^ 59
def prefixEnd_2816566 : Nat := 4983230072969 + 3 ^ 40 * 2816566 * 2
def baseEnd_2816566 : Nat := 482084051037177468757285

theorem tailTrace_2816566 : CollatzResearch.WordTrace tailWord_2816566 prefixEnd_2816566 482084051037177468757285 := by
  unfold tailWord_2816566
  simp only [CollatzResearch.WordTrace]
  refine ⟨6420537594629368001316347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 68485734342713258680707701 6420537594629368001316347)
  ·
    refine ⟨9630806391944052001974521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6420537594629368001316347 9630806391944052001974521)
    ·
      refine ⟨7223104793958039001480891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9630806391944052001974521 7223104793958039001480891)
      ·
        refine ⟨10834657190937058502221337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7223104793958039001480891 10834657190937058502221337)
        ·
          refine ⟨8125992893202793876666003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10834657190937058502221337 8125992893202793876666003)
          ·
            refine ⟨12188989339804190814999005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8125992893202793876666003 12188989339804190814999005)
            ·
              refine ⟨4570871002426571555624627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12188989339804190814999005 4570871002426571555624627)
              ·
                refine ⟨6856306503639857333436941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4570871002426571555624627 6856306503639857333436941)
                ·
                  refine ⟨2571114938864946500038853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6856306503639857333436941 2571114938864946500038853)
                  ·
                    refine ⟨482084051037177468757285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2571114938864946500038853 482084051037177468757285)
                    ·
                      rfl

theorem cell23_2816566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 3, 1, 3, 4].length) (baseStart_2816566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2816566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2816566 prefixEnd_2816566 := by exact prefixLift 2816566
  have htrace : WordTrace (prefixWord ++ tailWord_2816566) baseStart_2816566 baseEnd_2816566 := by
    simpa [prefixWord, tailWord_2816566, baseEnd_2816566] using wordTrace_append hprefix tailTrace_2816566
  have hstable : (prefixWord ++ tailWord_2816566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2816566).length < 2 ^ (prefixWord ++ tailWord_2816566).sum := by decide
  have hdescent : baseEnd_2816566 < baseStart_2816566 := by decide
  rcases family_descends (prefixWord ++ tailWord_2816566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2816592 : List Nat := [2, 1, 1, 1, 1, 3, 2, 6, 1, 5]
def baseStart_2816592 : Nat := 118140960795 + 2816592 * 2 ^ 59
def prefixEnd_2816592 : Nat := 4983230072969 + 3 ^ 40 * 2816592 * 2
def baseEnd_2816592 : Nat := 482088501202849768182245

theorem tailTrace_2816592 : CollatzResearch.WordTrace tailWord_2816592 prefixEnd_2816592 482088501202849768182245 := by
  unfold tailWord_2816592
  simp only [CollatzResearch.WordTrace]
  refine ⟨51364774905987847230754015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68486366541317129641005353 51364774905987847230754015)
  ·
    refine ⟨77047162358981770846131023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51364774905987847230754015 77047162358981770846131023)
    ·
      refine ⟨115570743538472656269196535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77047162358981770846131023 115570743538472656269196535)
      ·
        refine ⟨173356115307708984403794803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115570743538472656269196535 173356115307708984403794803)
        ·
          refine ⟨260034172961563476605692205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173356115307708984403794803 260034172961563476605692205)
          ·
            refine ⟨97512814860586303727134577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 260034172961563476605692205 97512814860586303727134577)
            ·
              refine ⟨73134611145439727795350933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97512814860586303727134577 73134611145439727795350933)
              ·
                refine ⟨3428184897442487240407075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 73134611145439727795350933 3428184897442487240407075)
                ·
                  refine ⟨5142277346163730860610613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3428184897442487240407075 5142277346163730860610613)
                  ·
                    refine ⟨482088501202849768182245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5142277346163730860610613 482088501202849768182245)
                    ·
                      rfl

theorem cell23_2816592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 6, 1, 5].length) (baseStart_2816592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2816592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2816592 prefixEnd_2816592 := by exact prefixLift 2816592
  have htrace : WordTrace (prefixWord ++ tailWord_2816592) baseStart_2816592 baseEnd_2816592 := by
    simpa [prefixWord, tailWord_2816592, baseEnd_2816592] using wordTrace_append hprefix tailTrace_2816592
  have hstable : (prefixWord ++ tailWord_2816592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2816592).length < 2 ^ (prefixWord ++ tailWord_2816592).sum := by decide
  have hdescent : baseEnd_2816592 < baseStart_2816592 := by decide
  rcases family_descends (prefixWord ++ tailWord_2816592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2816623 : List Nat := [1, 1, 2, 1, 3, 2, 6, 2, 1, 1, 3]
def baseStart_2816623 : Nat := 118140960795 + 2816623 * 2 ^ 59
def prefixEnd_2816623 : Nat := 4983230072969 + 3 ^ 40 * 2816623 * 2
def baseEnd_2816623 : Nat := 1446281421508838683259093

theorem tailTrace_2816623 : CollatzResearch.WordTrace tailWord_2816623 prefixEnd_2816623 1446281421508838683259093 := by
  unfold tailWord_2816623
  simp only [CollatzResearch.WordTrace]
  refine ⟨102730680474863386755886523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68487120316575591170591015 102730680474863386755886523)
  ·
    refine ⟨154096020712295080133829785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102730680474863386755886523 154096020712295080133829785)
    ·
      refine ⟨115572015534221310100372339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154096020712295080133829785 115572015534221310100372339)
      ·
        refine ⟨173358023301331965150558509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115572015534221310100372339 173358023301331965150558509)
        ·
          refine ⟨65009258737999486931459441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 173358023301331965150558509 65009258737999486931459441)
          ·
            refine ⟨48756944053499615198594581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65009258737999486931459441 48756944053499615198594581)
            ·
              refine ⟨2285481752507794462434121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 48756944053499615198594581 2285481752507794462434121)
              ·
                refine ⟨1714111314380845846825591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2285481752507794462434121 1714111314380845846825591)
                ·
                  refine ⟨2571166971571268770238387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1714111314380845846825591 2571166971571268770238387)
                  ·
                    refine ⟨3856750457356903155357581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2571166971571268770238387 3856750457356903155357581)
                    ·
                      refine ⟨1446281421508838683259093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3856750457356903155357581 1446281421508838683259093)
                      ·
                        rfl

theorem cell23_2816623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 6, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 6, 2, 1, 1, 3].length) (baseStart_2816623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2816623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2816623 prefixEnd_2816623 := by exact prefixLift 2816623
  have htrace : WordTrace (prefixWord ++ tailWord_2816623) baseStart_2816623 baseEnd_2816623 := by
    simpa [prefixWord, tailWord_2816623, baseEnd_2816623] using wordTrace_append hprefix tailTrace_2816623
  have hstable : (prefixWord ++ tailWord_2816623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2816623).length < 2 ^ (prefixWord ++ tailWord_2816623).sum := by decide
  have hdescent : baseEnd_2816623 < baseStart_2816623 := by decide
  rcases family_descends (prefixWord ++ tailWord_2816623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2816635 : List Nat := [1, 1, 1, 1, 1, 4, 2, 12]
def baseStart_2816635 : Nat := 118140960795 + 2816635 * 2 ^ 59
def prefixEnd_2816635 : Nat := 4983230072969 + 3 ^ 40 * 2816635 * 2
def baseEnd_2816635 : Nat := 53566206788025653196631

theorem tailTrace_2816635 : CollatzResearch.WordTrace tailWord_2816635 prefixEnd_2816635 53566206788025653196631 := by
  unfold tailWord_2816635
  simp only [CollatzResearch.WordTrace]
  refine ⟨102731118150819912805323359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68487412100546608536882239 102731118150819912805323359)
  ·
    refine ⟨154096677226229869207985039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102731118150819912805323359 154096677226229869207985039)
    ·
      refine ⟨231145015839344803811977559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154096677226229869207985039 231145015839344803811977559)
      ·
        refine ⟨346717523759017205717966339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 231145015839344803811977559 346717523759017205717966339)
        ·
          refine ⟨520076285638525808576949509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 346717523759017205717966339 520076285638525808576949509)
          ·
            refine ⟨97514303557223589108178033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 520076285638525808576949509 97514303557223589108178033)
            ·
              refine ⟨73135727667917691831133525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97514303557223589108178033 73135727667917691831133525)
              ·
                refine ⟨53566206788025653196631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 73135727667917691831133525 53566206788025653196631)
                ·
                  rfl

theorem cell23_2816635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 12].length) (baseStart_2816635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2816635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2816635 prefixEnd_2816635 := by exact prefixLift 2816635
  have htrace : WordTrace (prefixWord ++ tailWord_2816635) baseStart_2816635 baseEnd_2816635 := by
    simpa [prefixWord, tailWord_2816635, baseEnd_2816635] using wordTrace_append hprefix tailTrace_2816635
  have hstable : (prefixWord ++ tailWord_2816635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2816635).length < 2 ^ (prefixWord ++ tailWord_2816635).sum := by decide
  have hdescent : baseEnd_2816635 < baseStart_2816635 := by decide
  rcases family_descends (prefixWord ++ tailWord_2816635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2816649 : List Nat := [1, 2, 1, 1, 4, 1, 1, 6, 1, 2, 3]
def baseStart_2816649 : Nat := 118140960795 + 2816649 * 2 ^ 59
def prefixEnd_2816649 : Nat := 4983230072969 + 3 ^ 40 * 2816649 * 2
def baseEnd_2816649 : Nat := 1446294772005855581533973

theorem tailTrace_2816649 : CollatzResearch.WordTrace tailWord_2816649 prefixEnd_2816649 1446294772005855581533973 := by
  unfold tailWord_2816649
  simp only [CollatzResearch.WordTrace]
  refine ⟨102731628772769193196333001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68487752515179462130888667 102731628772769193196333001)
  ·
    refine ⟨77048721579576894897249751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102731628772769193196333001 77048721579576894897249751)
    ·
      refine ⟨115573082369365342345874627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77048721579576894897249751 115573082369365342345874627)
      ·
        refine ⟨173359623554048013518811941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115573082369365342345874627 173359623554048013518811941)
        ·
          refine ⟨32504929416384002534777239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 173359623554048013518811941 32504929416384002534777239)
          ·
            refine ⟨48757394124576003802165859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32504929416384002534777239 48757394124576003802165859)
            ·
              refine ⟨73136091186864005703248789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48757394124576003802165859 73136091186864005703248789)
              ·
                refine ⟨3428254274384250267339787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 73136091186864005703248789 3428254274384250267339787)
                ·
                  refine ⟨5142381411576375401009681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3428254274384250267339787 5142381411576375401009681)
                  ·
                    refine ⟨3856786058682281550757261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5142381411576375401009681 3856786058682281550757261)
                    ·
                      refine ⟨1446294772005855581533973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3856786058682281550757261 1446294772005855581533973)
                      ·
                        rfl

theorem cell23_2816649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 6, 1, 2, 3].length) (baseStart_2816649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2816649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2816649 prefixEnd_2816649 := by exact prefixLift 2816649
  have htrace : WordTrace (prefixWord ++ tailWord_2816649) baseStart_2816649 baseEnd_2816649 := by
    simpa [prefixWord, tailWord_2816649, baseEnd_2816649] using wordTrace_append hprefix tailTrace_2816649
  have hstable : (prefixWord ++ tailWord_2816649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2816649).length < 2 ^ (prefixWord ++ tailWord_2816649).sum := by decide
  have hdescent : baseEnd_2816649 < baseStart_2816649 := by decide
  rcases family_descends (prefixWord ++ tailWord_2816649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2816650 : List Nat := [3, 1, 2, 3, 4, 1, 1, 1, 2, 3, 2]
def baseStart_2816650 : Nat := 118140960795 + 2816650 * 2 ^ 59
def prefixEnd_2816650 : Nat := 4983230072969 + 3 ^ 40 * 2816650 * 2
def baseEnd_2816650 : Nat := 1446295285486510077621469

theorem tailTrace_2816650 : CollatzResearch.WordTrace tailWord_2816650 prefixEnd_2816650 1446295285486510077621469 := by
  unfold tailWord_2816650
  simp only [CollatzResearch.WordTrace]
  refine ⟨25682916311441392591779851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68487776830510380244746269 25682916311441392591779851)
  ·
    refine ⟨38524374467162088887669777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25682916311441392591779851 38524374467162088887669777)
    ·
      refine ⟨28893280850371566665752333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38524374467162088887669777 28893280850371566665752333)
      ·
        refine ⟨10834980318889337499657125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28893280850371566665752333 10834980318889337499657125)
        ·
          refine ⟨2031558809791750781185711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10834980318889337499657125 2031558809791750781185711)
          ·
            refine ⟨3047338214687626171778567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2031558809791750781185711 3047338214687626171778567)
            ·
              refine ⟨4571007322031439257667851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3047338214687626171778567 4571007322031439257667851)
              ·
                refine ⟨6856510983047158886501777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4571007322031439257667851 6856510983047158886501777)
                ·
                  refine ⟨5142383237285369164876333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6856510983047158886501777 5142383237285369164876333)
                  ·
                    refine ⟨1928393713982013436828625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5142383237285369164876333 1928393713982013436828625)
                    ·
                      refine ⟨1446295285486510077621469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1928393713982013436828625 1446295285486510077621469)
                      ·
                        rfl

theorem cell23_2816650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 1, 1, 2, 3, 2].length) (baseStart_2816650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2816650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2816650 prefixEnd_2816650 := by exact prefixLift 2816650
  have htrace : WordTrace (prefixWord ++ tailWord_2816650) baseStart_2816650 baseEnd_2816650 := by
    simpa [prefixWord, tailWord_2816650, baseEnd_2816650] using wordTrace_append hprefix tailTrace_2816650
  have hstable : (prefixWord ++ tailWord_2816650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2816650).length < 2 ^ (prefixWord ++ tailWord_2816650).sum := by decide
  have hdescent : baseEnd_2816650 < baseStart_2816650 := by decide
  rcases family_descends (prefixWord ++ tailWord_2816650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2816673 : List Nat := [1, 2, 3, 3, 3, 2, 1, 2, 2, 4]
def baseStart_2816673 : Nat := 118140960795 + 2816673 * 2 ^ 59
def prefixEnd_2816673 : Nat := 4983230072969 + 3 ^ 40 * 2816673 * 2
def baseEnd_2816673 : Nat := 482102365180521162544621

theorem tailTrace_2816673 : CollatzResearch.WordTrace tailWord_2816673 prefixEnd_2816673 482102365180521162544621 := by
  unfold tailWord_2816673
  simp only [CollatzResearch.WordTrace]
  refine ⟨102732504124682245295206673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68488336083121496863471115 102732504124682245295206673)
  ·
    refine ⟨77049378093511683971405005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102732504124682245295206673 77049378093511683971405005)
    ·
      refine ⟨28893516785066881489276877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77049378093511683971405005 28893516785066881489276877)
      ·
        refine ⟨10835068794400080558478829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28893516785066881489276877 10835068794400080558478829)
        ·
          refine ⟨4063150797900030209429561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10835068794400080558478829 4063150797900030209429561)
          ·
            refine ⟨3047363098425022657072171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4063150797900030209429561 3047363098425022657072171)
            ·
              refine ⟨4571044647637533985608257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3047363098425022657072171 4571044647637533985608257)
              ·
                refine ⟨3428283485728150489206193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4571044647637533985608257 3428283485728150489206193)
                ·
                  refine ⟨2571212614296112866904645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3428283485728150489206193 2571212614296112866904645)
                  ·
                    refine ⟨482102365180521162544621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2571212614296112866904645 482102365180521162544621)
                    ·
                      rfl

theorem cell23_2816673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 1, 2, 2, 4].length) (baseStart_2816673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2816673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2816673 prefixEnd_2816673 := by exact prefixLift 2816673
  have htrace : WordTrace (prefixWord ++ tailWord_2816673) baseStart_2816673 baseEnd_2816673 := by
    simpa [prefixWord, tailWord_2816673, baseEnd_2816673] using wordTrace_append hprefix tailTrace_2816673
  have hstable : (prefixWord ++ tailWord_2816673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2816673).length < 2 ^ (prefixWord ++ tailWord_2816673).sum := by decide
  have hdescent : baseEnd_2816673 < baseStart_2816673 := by decide
  rcases family_descends (prefixWord ++ tailWord_2816673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2816749 : List Nat := [1, 5, 1, 2, 1, 1, 2, 1, 1, 4, 4]
def baseStart_2816749 : Nat := 118140960795 + 2816749 * 2 ^ 59
def prefixEnd_2816749 : Nat := 4983230072969 + 3 ^ 40 * 2816749 * 2
def baseEnd_2816749 : Nat := 1446346120071305190283513

theorem tailTrace_2816749 : CollatzResearch.WordTrace tailWord_2816749 prefixEnd_2816749 1446346120071305190283513 := by
  unfold tailWord_2816749
  simp only [CollatzResearch.WordTrace]
  refine ⟨102735276072406910274973301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68490184048271273516648867 102735276072406910274973301)
  ·
    refine ⟨9631432131788147838278747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 102735276072406910274973301 9631432131788147838278747)
    ·
      refine ⟨14447148197682221757418121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9631432131788147838278747 14447148197682221757418121)
      ·
        refine ⟨10835361148261666318063591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14447148197682221757418121 10835361148261666318063591)
        ·
          refine ⟨16253041722392499477095387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10835361148261666318063591 16253041722392499477095387)
          ·
            refine ⟨24379562583588749215643081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16253041722392499477095387 24379562583588749215643081)
            ·
              refine ⟨18284671937691561911732311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24379562583588749215643081 18284671937691561911732311)
              ·
                refine ⟨27427007906537342867598467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18284671937691561911732311 27427007906537342867598467)
                ·
                  refine ⟨41140511859806014301397701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27427007906537342867598467 41140511859806014301397701)
                  ·
                    refine ⟨7713845973713627681512069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41140511859806014301397701 7713845973713627681512069)
                    ·
                      refine ⟨1446346120071305190283513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7713845973713627681512069 1446346120071305190283513)
                      ·
                        rfl

theorem cell23_2816749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 1, 1, 4, 4].length) (baseStart_2816749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2816749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2816749 prefixEnd_2816749 := by exact prefixLift 2816749
  have htrace : WordTrace (prefixWord ++ tailWord_2816749) baseStart_2816749 baseEnd_2816749 := by
    simpa [prefixWord, tailWord_2816749, baseEnd_2816749] using wordTrace_append hprefix tailTrace_2816749
  have hstable : (prefixWord ++ tailWord_2816749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2816749).length < 2 ^ (prefixWord ++ tailWord_2816749).sum := by decide
  have hdescent : baseEnd_2816749 < baseStart_2816749 := by decide
  rcases family_descends (prefixWord ++ tailWord_2816749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2816753 : List Nat := [1, 2, 2, 2, 2, 2, 3, 3, 2, 2, 2]
def baseStart_2816753 : Nat := 118140960795 + 2816753 * 2 ^ 59
def prefixEnd_2816753 : Nat := 4983230072969 + 3 ^ 40 * 2816753 * 2
def baseEnd_2816753 : Nat := 1446348173993923174633495

theorem tailTrace_2816753 : CollatzResearch.WordTrace tailWord_2816753 prefixEnd_2816753 1446348173993923174633495 := by
  unfold tailWord_2816753
  simp only [CollatzResearch.WordTrace]
  refine ⟨102735421964392418958118913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68490281309594945972079275 102735421964392418958118913)
  ·
    refine ⟨77051566473294314218589185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102735421964392418958118913 77051566473294314218589185)
    ·
      refine ⟨57788674854970735663941889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77051566473294314218589185 57788674854970735663941889)
      ·
        refine ⟨43341506141228051747956417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57788674854970735663941889 43341506141228051747956417)
        ·
          refine ⟨32506129605921038810967313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43341506141228051747956417 32506129605921038810967313)
          ·
            refine ⟨24379597204440779108225485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32506129605921038810967313 24379597204440779108225485)
            ·
              refine ⟨9142348951665292165584557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24379597204440779108225485 9142348951665292165584557)
              ·
                refine ⟨3428380856874484562094209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9142348951665292165584557 3428380856874484562094209)
                ·
                  refine ⟨2571285642655863421570657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3428380856874484562094209 2571285642655863421570657)
                  ·
                    refine ⟨1928464231991897566177993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2571285642655863421570657 1928464231991897566177993)
                    ·
                      refine ⟨1446348173993923174633495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1928464231991897566177993 1446348173993923174633495)
                      ·
                        rfl

theorem cell23_2816753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 3, 3, 2, 2, 2].length) (baseStart_2816753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2816753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2816753 prefixEnd_2816753 := by exact prefixLift 2816753
  have htrace : WordTrace (prefixWord ++ tailWord_2816753) baseStart_2816753 baseEnd_2816753 := by
    simpa [prefixWord, tailWord_2816753, baseEnd_2816753] using wordTrace_append hprefix tailTrace_2816753
  have hstable : (prefixWord ++ tailWord_2816753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2816753).length < 2 ^ (prefixWord ++ tailWord_2816753).sum := by decide
  have hdescent : baseEnd_2816753 < baseStart_2816753 := by decide
  rcases family_descends (prefixWord ++ tailWord_2816753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2816757 : List Nat := [1, 3, 6, 1, 1, 1, 1, 1, 3, 3, 2]
def baseStart_2816757 : Nat := 118140960795 + 2816757 * 2 ^ 59
def prefixEnd_2816757 : Nat := 4983230072969 + 3 ^ 40 * 2816757 * 2
def baseEnd_2816757 : Nat := 1446350227916541158983477

theorem tailTrace_2816757 : CollatzResearch.WordTrace tailWord_2816757 prefixEnd_2816757 1446350227916541158983477 := by
  unfold tailWord_2816757
  simp only [CollatzResearch.WordTrace]
  refine ⟨102735567856377927641264525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68490378570918618427509683 102735567856377927641264525)
  ·
    refine ⟨38525837946141722865474197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102735567856377927641264525 38525837946141722865474197)
    ·
      refine ⟨1805898653725393259319103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 38525837946141722865474197 1805898653725393259319103)
      ·
        refine ⟨2708847980588089888978655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1805898653725393259319103 2708847980588089888978655)
        ·
          refine ⟨4063271970882134833467983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2708847980588089888978655 4063271970882134833467983)
          ·
            refine ⟨6094907956323202250201975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4063271970882134833467983 6094907956323202250201975)
            ·
              refine ⟨9142361934484803375302963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6094907956323202250201975 9142361934484803375302963)
              ·
                refine ⟨13713542901727205062954445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9142361934484803375302963 13713542901727205062954445)
                ·
                  refine ⟨5142578588147701898607917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13713542901727205062954445 5142578588147701898607917)
                  ·
                    refine ⟨1928466970555388211977969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5142578588147701898607917 1928466970555388211977969)
                    ·
                      refine ⟨1446350227916541158983477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1928466970555388211977969 1446350227916541158983477)
                      ·
                        rfl

theorem cell23_2816757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 1, 1, 3, 3, 2].length) (baseStart_2816757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2816757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2816757 prefixEnd_2816757 := by exact prefixLift 2816757
  have htrace : WordTrace (prefixWord ++ tailWord_2816757) baseStart_2816757 baseEnd_2816757 := by
    simpa [prefixWord, tailWord_2816757, baseEnd_2816757] using wordTrace_append hprefix tailTrace_2816757
  have hstable : (prefixWord ++ tailWord_2816757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2816757).length < 2 ^ (prefixWord ++ tailWord_2816757).sum := by decide
  have hdescent : baseEnd_2816757 < baseStart_2816757 := by decide
  rcases family_descends (prefixWord ++ tailWord_2816757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2816769 : List Nat := [1, 2, 4, 1, 1, 1, 1, 2, 4, 3, 3]
def baseStart_2816769 : Nat := 118140960795 + 2816769 * 2 ^ 59
def prefixEnd_2816769 : Nat := 4983230072969 + 3 ^ 40 * 2816769 * 2
def baseEnd_2816769 : Nat := 1446356389684395112033421

theorem tailTrace_2816769 : CollatzResearch.WordTrace tailWord_2816769 prefixEnd_2816769 1446356389684395112033421 := by
  unfold tailWord_2816769
  simp only [CollatzResearch.WordTrace]
  refine ⟨102736005532334453690701361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68490670354889635793800907 102736005532334453690701361)
  ·
    refine ⟨77052004149250840268026021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102736005532334453690701361 77052004149250840268026021)
    ·
      refine ⟨14447250777984532550254879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 77052004149250840268026021 14447250777984532550254879)
      ·
        refine ⟨21670876166976798825382319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14447250777984532550254879 21670876166976798825382319)
        ·
          refine ⟨32506314250465198238073479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21670876166976798825382319 32506314250465198238073479)
          ·
            refine ⟨48759471375697797357110219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32506314250465198238073479 48759471375697797357110219)
            ·
              refine ⟨73139207063546696035665329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48759471375697797357110219 73139207063546696035665329)
              ·
                refine ⟨54854405297660022026748997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73139207063546696035665329 54854405297660022026748997)
                ·
                  refine ⟨10285200993311254130015437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 54854405297660022026748997 10285200993311254130015437)
                  ·
                    refine ⟨3856950372491720298755789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10285200993311254130015437 3856950372491720298755789)
                    ·
                      refine ⟨1446356389684395112033421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3856950372491720298755789 1446356389684395112033421)
                      ·
                        rfl

theorem cell23_2816769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 2, 4, 3, 3].length) (baseStart_2816769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2816769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2816769 prefixEnd_2816769 := by exact prefixLift 2816769
  have htrace : WordTrace (prefixWord ++ tailWord_2816769) baseStart_2816769 baseEnd_2816769 := by
    simpa [prefixWord, tailWord_2816769, baseEnd_2816769] using wordTrace_append hprefix tailTrace_2816769
  have hstable : (prefixWord ++ tailWord_2816769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2816769).length < 2 ^ (prefixWord ++ tailWord_2816769).sum := by decide
  have hdescent : baseEnd_2816769 < baseStart_2816769 := by decide
  rcases family_descends (prefixWord ++ tailWord_2816769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2816789 : List Nat := [1, 3, 2, 1, 2, 2, 1, 4, 2, 5]
def baseStart_2816789 : Nat := 118140960795 + 2816789 * 2 ^ 59
def prefixEnd_2816789 : Nat := 4983230072969 + 3 ^ 40 * 2816789 * 2
def baseEnd_2816789 : Nat := 482122219765828344594443

theorem tailTrace_2816789 : CollatzResearch.WordTrace tailWord_2816789 prefixEnd_2816789 482122219765828344594443 := by
  unfold tailWord_2816789
  simp only [CollatzResearch.WordTrace]
  refine ⟨102736734992261997106429421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68491156661507998070952947 102736734992261997106429421)
  ·
    refine ⟨38526275622098248914911033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102736734992261997106429421 38526275622098248914911033)
    ·
      refine ⟨28894706716573686686183275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38526275622098248914911033 28894706716573686686183275)
      ·
        refine ⟨43342060074860530029274913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28894706716573686686183275 43342060074860530029274913)
        ·
          refine ⟨32506545056145397521956185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43342060074860530029274913 32506545056145397521956185)
          ·
            refine ⟨24379908792109048141467139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32506545056145397521956185 24379908792109048141467139)
            ·
              refine ⟨36569863188163572212200709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24379908792109048141467139 36569863188163572212200709)
              ·
                refine ⟨6856849347780669789787633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36569863188163572212200709 6856849347780669789787633)
                ·
                  refine ⟨5142637010835502342340725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6856849347780669789787633 5142637010835502342340725)
                  ·
                    refine ⟨482122219765828344594443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5142637010835502342340725 482122219765828344594443)
                    ·
                      rfl

theorem cell23_2816789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 4, 2, 5].length) (baseStart_2816789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2816789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2816789 prefixEnd_2816789 := by exact prefixLift 2816789
  have htrace : WordTrace (prefixWord ++ tailWord_2816789) baseStart_2816789 baseEnd_2816789 := by
    simpa [prefixWord, tailWord_2816789, baseEnd_2816789] using wordTrace_append hprefix tailTrace_2816789
  have hstable : (prefixWord ++ tailWord_2816789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2816789).length < 2 ^ (prefixWord ++ tailWord_2816789).sum := by decide
  have hdescent : baseEnd_2816789 < baseStart_2816789 := by decide
  rcases family_descends (prefixWord ++ tailWord_2816789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2816796 : List Nat := [2, 2, 3, 1, 1, 3, 1, 1, 2, 5, 2]
def baseStart_2816796 : Nat := 118140960795 + 2816796 * 2 ^ 59
def prefixEnd_2816796 : Nat := 4983230072969 + 3 ^ 40 * 2816796 * 2
def baseEnd_2816796 : Nat := 1446370253662066506395797

theorem tailTrace_2816796 : CollatzResearch.WordTrace tailWord_2816796 prefixEnd_2816796 1446370253662066506395797 := by
  unfold tailWord_2816796
  simp only [CollatzResearch.WordTrace]
  refine ⟨51368495151618318650967121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68491326868824424867956161 51368495151618318650967121)
  ·
    refine ⟨38526371363713738988225341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51368495151618318650967121 38526371363713738988225341)
    ·
      refine ⟨14447389261392652120584503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38526371363713738988225341 14447389261392652120584503)
      ·
        refine ⟨21671083892088978180876755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14447389261392652120584503 21671083892088978180876755)
        ·
          refine ⟨32506625838133467271315133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21671083892088978180876755 32506625838133467271315133)
          ·
            refine ⟨12189984689300050226743175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32506625838133467271315133 12189984689300050226743175)
            ·
              refine ⟨18284977033950075340114763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12189984689300050226743175 18284977033950075340114763)
              ·
                refine ⟨27427465550925113010172145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18284977033950075340114763 27427465550925113010172145)
                ·
                  refine ⟨20570599163193834757629109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27427465550925113010172145 20570599163193834757629109)
                  ·
                    refine ⟨1928493671549422008527729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 20570599163193834757629109 1928493671549422008527729)
                    ·
                      refine ⟨1446370253662066506395797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1928493671549422008527729 1446370253662066506395797)
                      ·
                        rfl

theorem cell23_2816796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 1, 2, 5, 2].length) (baseStart_2816796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2816796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2816796 prefixEnd_2816796 := by exact prefixLift 2816796
  have htrace : WordTrace (prefixWord ++ tailWord_2816796) baseStart_2816796 baseEnd_2816796 := by
    simpa [prefixWord, tailWord_2816796, baseEnd_2816796] using wordTrace_append hprefix tailTrace_2816796
  have hstable : (prefixWord ++ tailWord_2816796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2816796).length < 2 ^ (prefixWord ++ tailWord_2816796).sum := by decide
  have hdescent : baseEnd_2816796 < baseStart_2816796 := by decide
  rcases family_descends (prefixWord ++ tailWord_2816796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2816799 : List Nat := [1, 1, 2, 4, 2, 2, 2, 1, 1, 2, 5]
def baseStart_2816799 : Nat := 118140960795 + 2816799 * 2 ^ 59
def prefixEnd_2816799 : Nat := 4983230072969 + 3 ^ 40 * 2816799 * 2
def baseEnd_2816799 : Nat := 1446371794104029994658283

theorem tailTrace_2816799 : CollatzResearch.WordTrace tailWord_2816799 prefixEnd_2816799 1446371794104029994658283 := by
  unfold tailWord_2816799
  simp only [CollatzResearch.WordTrace]
  refine ⟨102737099722225768814293451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68491399814817179209528967 102737099722225768814293451)
  ·
    refine ⟨154105649583338653221440177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102737099722225768814293451 154105649583338653221440177)
    ·
      refine ⟨115579237187503989916080133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154105649583338653221440177 115579237187503989916080133)
      ·
        refine ⟨21671106972656998109265025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 115579237187503989916080133 21671106972656998109265025)
        ·
          refine ⟨16253330229492748581948769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21671106972656998109265025 16253330229492748581948769)
          ·
            refine ⟨12189997672119561436461577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16253330229492748581948769 12189997672119561436461577)
            ·
              refine ⟨9142498254089671077346183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12189997672119561436461577 9142498254089671077346183)
              ·
                refine ⟨13713747381134506616019275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9142498254089671077346183 13713747381134506616019275)
                ·
                  refine ⟨20570621071701759924028913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13713747381134506616019275 20570621071701759924028913)
                  ·
                    refine ⟨15427965803776319943021685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20570621071701759924028913 15427965803776319943021685)
                    ·
                      refine ⟨1446371794104029994658283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15427965803776319943021685 1446371794104029994658283)
                      ·
                        rfl

theorem cell23_2816799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 2, 1, 1, 2, 5].length) (baseStart_2816799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2816799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2816799 prefixEnd_2816799 := by exact prefixLift 2816799
  have htrace : WordTrace (prefixWord ++ tailWord_2816799) baseStart_2816799 baseEnd_2816799 := by
    simpa [prefixWord, tailWord_2816799, baseEnd_2816799] using wordTrace_append hprefix tailTrace_2816799
  have hstable : (prefixWord ++ tailWord_2816799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2816799).length < 2 ^ (prefixWord ++ tailWord_2816799).sum := by decide
  have hdescent : baseEnd_2816799 < baseStart_2816799 := by decide
  rcases family_descends (prefixWord ++ tailWord_2816799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2816826 : List Nat := [3, 1, 1, 1, 6, 1, 1, 1, 1, 3, 4]
def baseStart_2816826 : Nat := 118140960795 + 2816826 * 2 ^ 59
def prefixEnd_2816826 : Nat := 4983230072969 + 3 ^ 40 * 2816826 * 2
def baseEnd_2816826 : Nat := 1446385658081701389020659

theorem tailTrace_2816826 : CollatzResearch.WordTrace tailWord_2816826 prefixEnd_2816826 1446385658081701389020659 := by
  unfold tailWord_2816826
  simp only [CollatzResearch.WordTrace]
  refine ⟨25684521123281988106381583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68492056328751968283684221 25684521123281988106381583)
  ·
    refine ⟨38526781684922982159572375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25684521123281988106381583 38526781684922982159572375)
    ·
      refine ⟨57790172527384473239358563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38526781684922982159572375 57790172527384473239358563)
      ·
        refine ⟨86685258791076709859037845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57790172527384473239358563 86685258791076709859037845)
        ·
          refine ⟨4063371505831720774642399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 86685258791076709859037845 4063371505831720774642399)
          ·
            refine ⟨6095057258747581161963599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4063371505831720774642399 6095057258747581161963599)
            ·
              refine ⟨9142585888121371742945399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6095057258747581161963599 9142585888121371742945399)
              ·
                refine ⟨13713878832182057614418099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9142585888121371742945399 13713878832182057614418099)
                ·
                  refine ⟨20570818248273086421627149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13713878832182057614418099 20570818248273086421627149)
                  ·
                    refine ⟨7714056843102407408110181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20570818248273086421627149 7714056843102407408110181)
                    ·
                      refine ⟨1446385658081701389020659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7714056843102407408110181 1446385658081701389020659)
                      ·
                        rfl

theorem cell23_2816826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 1, 1, 1, 3, 4].length) (baseStart_2816826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2816826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2816826 prefixEnd_2816826 := by exact prefixLift 2816826
  have htrace : WordTrace (prefixWord ++ tailWord_2816826) baseStart_2816826 baseEnd_2816826 := by
    simpa [prefixWord, tailWord_2816826, baseEnd_2816826] using wordTrace_append hprefix tailTrace_2816826
  have hstable : (prefixWord ++ tailWord_2816826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2816826).length < 2 ^ (prefixWord ++ tailWord_2816826).sum := by decide
  have hdescent : baseEnd_2816826 < baseStart_2816826 := by decide
  rcases family_descends (prefixWord ++ tailWord_2816826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2816846 : List Nat := [4, 1, 1, 1, 1, 1, 1, 6, 2, 2, 3]
def baseStart_2816846 : Nat := 118140960795 + 2816846 * 2 ^ 59
def prefixEnd_2816846 : Nat := 4983230072969 + 3 ^ 40 * 2816846 * 2
def baseEnd_2816846 : Nat := 1446395927694791310770567

theorem tailTrace_2816846 : CollatzResearch.WordTrace tailWord_2816846 prefixEnd_2816846 1446395927694791310770567 := by
  unfold tailWord_2816846
  simp only [CollatzResearch.WordTrace]
  refine ⟨12842351744131936980156799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68492542635370330560836261 12842351744131936980156799)
  ·
    refine ⟨19263527616197905470235199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12842351744131936980156799 19263527616197905470235199)
    ·
      refine ⟨28895291424296858205352799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19263527616197905470235199 28895291424296858205352799)
      ·
        refine ⟨43342937136445287308029199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28895291424296858205352799 43342937136445287308029199)
        ·
          refine ⟨65014405704667930962043799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43342937136445287308029199 65014405704667930962043799)
          ·
            refine ⟨97521608557001896443065699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65014405704667930962043799 97521608557001896443065699)
            ·
              refine ⟨146282412835502844664598549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97521608557001896443065699 146282412835502844664598549)
              ·
                refine ⟨6856988101664195843653057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 146282412835502844664598549 6856988101664195843653057)
                ·
                  refine ⟨5142741076248146882739793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6856988101664195843653057 5142741076248146882739793)
                  ·
                    refine ⟨3857055807186110162054845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5142741076248146882739793 3857055807186110162054845)
                    ·
                      refine ⟨1446395927694791310770567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3857055807186110162054845 1446395927694791310770567)
                      ·
                        rfl

theorem cell23_2816846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 6, 2, 2, 3].length) (baseStart_2816846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2816846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2816846 prefixEnd_2816846 := by exact prefixLift 2816846
  have htrace : WordTrace (prefixWord ++ tailWord_2816846) baseStart_2816846 baseEnd_2816846 := by
    simpa [prefixWord, tailWord_2816846, baseEnd_2816846] using wordTrace_append hprefix tailTrace_2816846
  have hstable : (prefixWord ++ tailWord_2816846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2816846).length < 2 ^ (prefixWord ++ tailWord_2816846).sum := by decide
  have hdescent : baseEnd_2816846 < baseStart_2816846 := by decide
  rcases family_descends (prefixWord ++ tailWord_2816846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2816853 : List Nat := [1, 3, 2, 2, 2, 1, 1, 6, 1, 4]
def baseStart_2816853 : Nat := 118140960795 + 2816853 * 2 ^ 59
def prefixEnd_2816853 : Nat := 4983230072969 + 3 ^ 40 * 2816853 * 2
def baseEnd_2816853 : Nat := 482133174019790927794345

theorem tailTrace_2816853 : CollatzResearch.WordTrace tailWord_2816853 prefixEnd_2816853 482133174019790927794345 := by
  unfold tailWord_2816853
  simp only [CollatzResearch.WordTrace]
  refine ⟨102739069264030136036759213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68492712842686757357839475 102739069264030136036759213)
  ·
    refine ⟨38527150974011301013784705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102739069264030136036759213 38527150974011301013784705)
    ·
      refine ⟨28895363230508475760338529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38527150974011301013784705 28895363230508475760338529)
      ·
        refine ⟨21671522422881356820253897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28895363230508475760338529 21671522422881356820253897)
        ·
          refine ⟨16253641817161017615190423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21671522422881356820253897 16253641817161017615190423)
          ·
            refine ⟨24380462725741526422785635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16253641817161017615190423 24380462725741526422785635)
            ·
              refine ⟨36570694088612289634178453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24380462725741526422785635 36570694088612289634178453)
              ·
                refine ⟨1714251285403701076602115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 36570694088612289634178453 1714251285403701076602115)
                ·
                  refine ⟨2571376928105551614903173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1714251285403701076602115 2571376928105551614903173)
                  ·
                    refine ⟨482133174019790927794345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2571376928105551614903173 482133174019790927794345)
                    ·
                      rfl

theorem cell23_2816853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 6, 1, 4].length) (baseStart_2816853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2816853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2816853 prefixEnd_2816853 := by exact prefixLift 2816853
  have htrace : WordTrace (prefixWord ++ tailWord_2816853) baseStart_2816853 baseEnd_2816853 := by
    simpa [prefixWord, tailWord_2816853, baseEnd_2816853] using wordTrace_append hprefix tailTrace_2816853
  have hstable : (prefixWord ++ tailWord_2816853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2816853).length < 2 ^ (prefixWord ++ tailWord_2816853).sum := by decide
  have hdescent : baseEnd_2816853 < baseStart_2816853 := by decide
  rcases family_descends (prefixWord ++ tailWord_2816853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2816879 : List Nat := [1, 1, 2, 1, 3, 1, 1, 5, 3, 5]
def baseStart_2816879 : Nat := 118140960795 + 2816879 * 2 ^ 59
def prefixEnd_2816879 : Nat := 4983230072969 + 3 ^ 40 * 2816879 * 2
def baseEnd_2816879 : Nat := 482137624185463227219305

theorem tailTrace_2816879 : CollatzResearch.WordTrace tailWord_2816879 prefixEnd_2816879 482137624185463227219305 := by
  unfold tailWord_2816879
  simp only [CollatzResearch.WordTrace]
  refine ⟨102740017561935942477205691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68493345041290628318137127 102740017561935942477205691)
  ·
    refine ⟨154110026342903913715808537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102740017561935942477205691 154110026342903913715808537)
    ·
      refine ⟨115582519757177935286856403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154110026342903913715808537 115582519757177935286856403)
      ·
        refine ⟨173373779635766902930284605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115582519757177935286856403 173373779635766902930284605)
        ·
          refine ⟨65015167363412588598856727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 173373779635766902930284605 65015167363412588598856727)
          ·
            refine ⟨97522751045118882898285091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65015167363412588598856727 97522751045118882898285091)
            ·
              refine ⟨146284126567678324347427637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97522751045118882898285091 146284126567678324347427637)
              ·
                refine ⟨13714136865719842907571341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 146284126567678324347427637 13714136865719842907571341)
                ·
                  refine ⟨5142801324644941090339253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13714136865719842907571341 5142801324644941090339253)
                  ·
                    refine ⟨482137624185463227219305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5142801324644941090339253 482137624185463227219305)
                    ·
                      rfl

theorem cell23_2816879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 5, 3, 5].length) (baseStart_2816879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2816879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2816879 prefixEnd_2816879 := by exact prefixLift 2816879
  have htrace : WordTrace (prefixWord ++ tailWord_2816879) baseStart_2816879 baseEnd_2816879 := by
    simpa [prefixWord, tailWord_2816879, baseEnd_2816879] using wordTrace_append hprefix tailTrace_2816879
  have hstable : (prefixWord ++ tailWord_2816879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2816879).length < 2 ^ (prefixWord ++ tailWord_2816879).sum := by decide
  have hdescent : baseEnd_2816879 < baseStart_2816879 := by decide
  rcases family_descends (prefixWord ++ tailWord_2816879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2816903 : List Nat := [1, 1, 4, 2, 3, 1, 1, 1, 4, 3, 2]
def baseStart_2816903 : Nat := 118140960795 + 2816903 * 2 ^ 59
def prefixEnd_2816903 : Nat := 4983230072969 + 3 ^ 40 * 2816903 * 2
def baseEnd_2816903 : Nat := 1446425196092097587757805

theorem tailTrace_2816903 : CollatzResearch.WordTrace tailWord_2816903 prefixEnd_2816903 1446425196092097587757805 := by
  unfold tailWord_2816903
  simp only [CollatzResearch.WordTrace]
  refine ⟨102740892913848994576079363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68493928609232663050719575 102740892913848994576079363)
  ·
    refine ⟨154111339370773491864119045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102740892913848994576079363 154111339370773491864119045)
    ·
      refine ⟨28895876132020029724522321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 154111339370773491864119045 28895876132020029724522321)
      ·
        refine ⟨21671907099015022293391741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28895876132020029724522321 21671907099015022293391741)
        ·
          refine ⟨8126965162130633360021903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21671907099015022293391741 8126965162130633360021903)
          ·
            refine ⟨12190447743195950040032855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8126965162130633360021903 12190447743195950040032855)
            ·
              refine ⟨18285671614793925060049283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12190447743195950040032855 18285671614793925060049283)
              ·
                refine ⟨27428507422190887590073925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18285671614793925060049283 27428507422190887590073925)
                ·
                  refine ⟨5142845141660791423138861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27428507422190887590073925 5142845141660791423138861)
                  ·
                    refine ⟨1928566928122796783677073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5142845141660791423138861 1928566928122796783677073)
                    ·
                      refine ⟨1446425196092097587757805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1928566928122796783677073 1446425196092097587757805)
                      ·
                        rfl

theorem cell23_2816903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 1, 4, 3, 2].length) (baseStart_2816903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2816903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2816903 prefixEnd_2816903 := by exact prefixLift 2816903
  have htrace : WordTrace (prefixWord ++ tailWord_2816903) baseStart_2816903 baseEnd_2816903 := by
    simpa [prefixWord, tailWord_2816903, baseEnd_2816903] using wordTrace_append hprefix tailTrace_2816903
  have hstable : (prefixWord ++ tailWord_2816903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2816903).length < 2 ^ (prefixWord ++ tailWord_2816903).sum := by decide
  have hdescent : baseEnd_2816903 < baseStart_2816903 := by decide
  rcases family_descends (prefixWord ++ tailWord_2816903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2816930 : List Nat := [3, 3, 1, 2, 2, 3, 1, 2, 1, 5]
def baseStart_2816930 : Nat := 118140960795 + 2816930 * 2 ^ 59
def prefixEnd_2816930 : Nat := 4983230072969 + 3 ^ 40 * 2816930 * 2
def baseEnd_2816930 : Nat := 482146353356589660706727

theorem tailTrace_2816930 : CollatzResearch.WordTrace tailWord_2816930 prefixEnd_2816930 482146353356589660706727 := by
  unfold tailWord_2816930
  simp only [CollatzResearch.WordTrace]
  refine ⟨25685469421187794546828061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68494585123167452124874829 25685469421187794546828061)
  ·
    refine ⟨9632051032945422955060523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25685469421187794546828061 9632051032945422955060523)
    ·
      refine ⟨14448076549418134432590785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9632051032945422955060523 14448076549418134432590785)
      ·
        refine ⟨10836057412063600824443089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14448076549418134432590785 10836057412063600824443089)
        ·
          refine ⟨8127043059047700618332317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10836057412063600824443089 8127043059047700618332317)
          ·
            refine ⟨3047641147142887731874619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8127043059047700618332317 3047641147142887731874619)
            ·
              refine ⟨4571461720714331597811929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3047641147142887731874619 4571461720714331597811929)
              ·
                refine ⟨3428596290535748698358947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4571461720714331597811929 3428596290535748698358947)
                ·
                  refine ⟨5142894435803623047538421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3428596290535748698358947 5142894435803623047538421)
                  ·
                    refine ⟨482146353356589660706727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5142894435803623047538421 482146353356589660706727)
                    ·
                      rfl

theorem cell23_2816930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 1, 2, 1, 5].length) (baseStart_2816930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2816930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2816930 prefixEnd_2816930 := by exact prefixLift 2816930
  have htrace : WordTrace (prefixWord ++ tailWord_2816930) baseStart_2816930 baseEnd_2816930 := by
    simpa [prefixWord, tailWord_2816930, baseEnd_2816930] using wordTrace_append hprefix tailTrace_2816930
  have hstable : (prefixWord ++ tailWord_2816930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2816930).length < 2 ^ (prefixWord ++ tailWord_2816930).sum := by decide
  have hdescent : baseEnd_2816930 < baseStart_2816930 := by decide
  rcases family_descends (prefixWord ++ tailWord_2816930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2816953 : List Nat := [1, 2, 1, 4, 2, 4, 1, 1, 1, 1, 5]
def baseStart_2816953 : Nat := 118140960795 + 2816953 * 2 ^ 59
def prefixEnd_2816953 : Nat := 4983230072969 + 3 ^ 40 * 2816953 * 2
def baseEnd_2816953 : Nat := 1446450870124822392132575

theorem tailTrace_2816953 : CollatzResearch.WordTrace tailWord_2816953 prefixEnd_2816953 1446450870124822392132575 := by
  unfold tailWord_2816953
  simp only [CollatzResearch.WordTrace]
  refine ⟨102742716563667853115399513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68495144375778568743599675 102742716563667853115399513)
  ·
    refine ⟨77057037422750889836549635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102742716563667853115399513 77057037422750889836549635)
    ·
      refine ⟨115585556134126334754824453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77057037422750889836549635 115585556134126334754824453)
      ·
        refine ⟨21672291775148687766529585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 115585556134126334754824453 21672291775148687766529585)
        ·
          refine ⟨16254218831361515824897189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21672291775148687766529585 16254218831361515824897189)
          ·
            refine ⟨3047666030880284217168223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16254218831361515824897189 3047666030880284217168223)
            ·
              refine ⟨4571499046320426325752335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3047666030880284217168223 4571499046320426325752335)
              ·
                refine ⟨6857248569480639488628503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4571499046320426325752335 6857248569480639488628503)
                ·
                  refine ⟨10285872854220959232942755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6857248569480639488628503 10285872854220959232942755)
                  ·
                    refine ⟨15428809281331438849414133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10285872854220959232942755 15428809281331438849414133)
                    ·
                      refine ⟨1446450870124822392132575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15428809281331438849414133 1446450870124822392132575)
                      ·
                        rfl

theorem cell23_2816953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 1, 1, 1, 1, 5].length) (baseStart_2816953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2816953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2816953 prefixEnd_2816953 := by exact prefixLift 2816953
  have htrace : WordTrace (prefixWord ++ tailWord_2816953) baseStart_2816953 baseEnd_2816953 := by
    simpa [prefixWord, tailWord_2816953, baseEnd_2816953] using wordTrace_append hprefix tailTrace_2816953
  have hstable : (prefixWord ++ tailWord_2816953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2816953).length < 2 ^ (prefixWord ++ tailWord_2816953).sum := by decide
  have hdescent : baseEnd_2816953 < baseStart_2816953 := by decide
  rcases family_descends (prefixWord ++ tailWord_2816953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2816959 : List Nat := [1, 1, 2, 2, 2, 1, 2, 2, 2, 2, 6]
def baseStart_2816959 : Nat := 118140960795 + 2816959 * 2 ^ 59
def prefixEnd_2816959 : Nat := 4983230072969 + 3 ^ 40 * 2816959 * 2
def baseEnd_2816959 : Nat := 1446453951008749368657547

theorem tailTrace_2816959 : CollatzResearch.WordTrace tailWord_2816959 prefixEnd_2816959 1446453951008749368657547 := by
  unfold tailWord_2816959
  simp only [CollatzResearch.WordTrace]
  refine ⟨102742935401646116140117931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68495290267764077426745287 102742935401646116140117931)
  ·
    refine ⟨154114403102469174210176897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102742935401646116140117931 154114403102469174210176897)
    ·
      refine ⟨115585802326851880657632673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154114403102469174210176897 115585802326851880657632673)
      ·
        refine ⟨86689351745138910493224505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115585802326851880657632673 86689351745138910493224505)
        ·
          refine ⟨65017013808854182869918379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86689351745138910493224505 65017013808854182869918379)
          ·
            refine ⟨97525520713281274304877569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65017013808854182869918379 97525520713281274304877569)
            ·
              refine ⟨73144140534960955728658177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97525520713281274304877569 73144140534960955728658177)
              ·
                refine ⟨54858105401220716796493633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73144140534960955728658177 54858105401220716796493633)
                ·
                  refine ⟨41143579050915537597370225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54858105401220716796493633 41143579050915537597370225)
                  ·
                    refine ⟨30857684288186653198027669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 41143579050915537597370225 30857684288186653198027669)
                    ·
                      refine ⟨1446453951008749368657547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 30857684288186653198027669 1446453951008749368657547)
                      ·
                        rfl

theorem cell23_2816959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 2, 2, 2, 6].length) (baseStart_2816959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2816959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2816959 prefixEnd_2816959 := by exact prefixLift 2816959
  have htrace : WordTrace (prefixWord ++ tailWord_2816959) baseStart_2816959 baseEnd_2816959 := by
    simpa [prefixWord, tailWord_2816959, baseEnd_2816959] using wordTrace_append hprefix tailTrace_2816959
  have hstable : (prefixWord ++ tailWord_2816959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2816959).length < 2 ^ (prefixWord ++ tailWord_2816959).sum := by decide
  have hdescent : baseEnd_2816959 < baseStart_2816959 := by decide
  rcases family_descends (prefixWord ++ tailWord_2816959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2817113 : List Nat := [1, 2, 1, 2, 2, 1, 2, 1, 3, 6, 2]
def baseStart_2817113 : Nat := 118140960795 + 2817113 * 2 ^ 59
def prefixEnd_2817113 : Nat := 4983230072969 + 3 ^ 40 * 2817113 * 2
def baseEnd_2817113 : Nat := 1446533027029541766131839

theorem tailTrace_2817113 : CollatzResearch.WordTrace tailWord_2817113 prefixEnd_2817113 1446533027029541766131839 := by
  unfold tailWord_2817113
  simp only [CollatzResearch.WordTrace]
  refine ⟨102748552243088200441223993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68499034828725466960815995 102748552243088200441223993)
  ·
    refine ⟨77061414182316150330917995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102748552243088200441223993 77061414182316150330917995)
    ·
      refine ⟨115592121273474225496376993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77061414182316150330917995 115592121273474225496376993)
      ·
        refine ⟨86694090955105669122282745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115592121273474225496376993 86694090955105669122282745)
        ·
          refine ⟨65020568216329251841712059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86694090955105669122282745 65020568216329251841712059)
          ·
            refine ⟨97530852324493877762568089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65020568216329251841712059 97530852324493877762568089)
            ·
              refine ⟨73148139243370408321926067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97530852324493877762568089 73148139243370408321926067)
              ·
                refine ⟨109722208865055612482889101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73148139243370408321926067 109722208865055612482889101)
                ·
                  refine ⟨41145828324395854681083413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 109722208865055612482889101 41145828324395854681083413)
                  ·
                    refine ⟨1928710702706055688175785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 41145828324395854681083413 1928710702706055688175785)
                    ·
                      refine ⟨1446533027029541766131839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1928710702706055688175785 1446533027029541766131839)
                      ·
                        rfl

theorem cell23_2817113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 1, 3, 6, 2].length) (baseStart_2817113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2817113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2817113 prefixEnd_2817113 := by exact prefixLift 2817113
  have htrace : WordTrace (prefixWord ++ tailWord_2817113) baseStart_2817113 baseEnd_2817113 := by
    simpa [prefixWord, tailWord_2817113, baseEnd_2817113] using wordTrace_append hprefix tailTrace_2817113
  have hstable : (prefixWord ++ tailWord_2817113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2817113).length < 2 ^ (prefixWord ++ tailWord_2817113).sum := by decide
  have hdescent : baseEnd_2817113 < baseStart_2817113 := by decide
  rcases family_descends (prefixWord ++ tailWord_2817113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2817130 : List Nat := [3, 1, 3, 2, 2, 1, 2, 2, 2, 1, 4]
def baseStart_2817130 : Nat := 118140960795 + 2817130 * 2 ^ 59
def prefixEnd_2817130 : Nat := 4983230072969 + 3 ^ 40 * 2817130 * 2
def baseEnd_2817130 : Nat := 1446541756200668199619261

theorem tailTrace_2817130 : CollatzResearch.WordTrace tailWord_2817130 prefixEnd_2817130 1446541756200668199619261 := by
  unfold tailWord_2817130
  simp only [CollatzResearch.WordTrace]
  refine ⟨25687293071006653086148211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68499448189351074896395229 25687293071006653086148211)
  ·
    refine ⟨38530939606509979629222317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25687293071006653086148211 38530939606509979629222317)
    ·
      refine ⟨14449102352441242360958369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38530939606509979629222317 14449102352441242360958369)
      ·
        refine ⟨10836826764330931770718777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14449102352441242360958369 10836826764330931770718777)
        ·
          refine ⟨8127620073248198828039083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10836826764330931770718777 8127620073248198828039083)
          ·
            refine ⟨12191430109872298242058625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8127620073248198828039083 12191430109872298242058625)
            ·
              refine ⟨9143572582404223681543969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12191430109872298242058625 9143572582404223681543969)
              ·
                refine ⟨6857679436803167761157977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9143572582404223681543969 6857679436803167761157977)
                ·
                  refine ⟨5143259577602375820868483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6857679436803167761157977 5143259577602375820868483)
                  ·
                    refine ⟨7714889366403563731302725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5143259577602375820868483 7714889366403563731302725)
                    ·
                      refine ⟨1446541756200668199619261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7714889366403563731302725 1446541756200668199619261)
                      ·
                        rfl

theorem cell23_2817130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 2, 2, 2, 1, 4].length) (baseStart_2817130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2817130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2817130 prefixEnd_2817130 := by exact prefixLift 2817130
  have htrace : WordTrace (prefixWord ++ tailWord_2817130) baseStart_2817130 baseEnd_2817130 := by
    simpa [prefixWord, tailWord_2817130, baseEnd_2817130] using wordTrace_append hprefix tailTrace_2817130
  have hstable : (prefixWord ++ tailWord_2817130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2817130).length < 2 ^ (prefixWord ++ tailWord_2817130).sum := by decide
  have hdescent : baseEnd_2817130 < baseStart_2817130 := by decide
  rcases family_descends (prefixWord ++ tailWord_2817130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2817203 : List Nat := [1, 1, 1, 2, 3, 2, 2, 1, 5, 1, 4]
def baseStart_2817203 : Nat := 118140960795 + 2817203 * 2 ^ 59
def prefixEnd_2817203 : Nat := 4983230072969 + 3 ^ 40 * 2817203 * 2
def baseEnd_2817203 : Nat := 1446579240288446414006425

theorem tailTrace_2817203 : CollatzResearch.WordTrace tailWord_2817203 prefixEnd_2817203 1446579240288446414006425 := by
  unfold tailWord_2817203
  simp only [CollatzResearch.WordTrace]
  refine ⟨102751834812762145812000263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68501223208508097208000175 102751834812762145812000263)
  ·
    refine ⟨154127752219143218718000395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102751834812762145812000263 154127752219143218718000395)
    ·
      refine ⟨231191628328714828077000593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154127752219143218718000395 231191628328714828077000593)
      ·
        refine ⟨173393721246536121057750445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 231191628328714828077000593 173393721246536121057750445)
        ·
          refine ⟨65022645467451045396656417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 173393721246536121057750445 65022645467451045396656417)
          ·
            refine ⟨48766984100588284047492313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65022645467451045396656417 48766984100588284047492313)
            ·
              refine ⟨36575238075441213035619235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48766984100588284047492313 36575238075441213035619235)
              ·
                refine ⟨54862857113161819553428853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36575238075441213035619235 54862857113161819553428853)
                ·
                  refine ⟨5143392854358920583133955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 54862857113161819553428853 5143392854358920583133955)
                  ·
                    refine ⟨7715089281538380874700933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5143392854358920583133955 7715089281538380874700933)
                    ·
                      refine ⟨1446579240288446414006425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7715089281538380874700933 1446579240288446414006425)
                      ·
                        rfl

theorem cell23_2817203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 1, 5, 1, 4].length) (baseStart_2817203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2817203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2817203 prefixEnd_2817203 := by exact prefixLift 2817203
  have htrace : WordTrace (prefixWord ++ tailWord_2817203) baseStart_2817203 baseEnd_2817203 := by
    simpa [prefixWord, tailWord_2817203, baseEnd_2817203] using wordTrace_append hprefix tailTrace_2817203
  have hstable : (prefixWord ++ tailWord_2817203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2817203).length < 2 ^ (prefixWord ++ tailWord_2817203).sum := by decide
  have hdescent : baseEnd_2817203 < baseStart_2817203 := by decide
  rcases family_descends (prefixWord ++ tailWord_2817203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2817217 : List Nat := [1, 2, 6, 1, 1, 1, 1, 4, 1, 5]
def baseStart_2817217 : Nat := 118140960795 + 2817217 * 2 ^ 59
def prefixEnd_2817217 : Nat := 4983230072969 + 3 ^ 40 * 2817217 * 2
def baseEnd_2817217 : Nat := 482195476339203119743787

theorem tailTrace_2817217 : CollatzResearch.WordTrace tailWord_2817217 prefixEnd_2817217 482195476339203119743787 := by
  unfold tailWord_2817217
  simp only [CollatzResearch.WordTrace]
  refine ⟨102752345434711426203009905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68501563623140950802006603 102752345434711426203009905)
  ·
    refine ⟨77064259076033569652257429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102752345434711426203009905 77064259076033569652257429)
    ·
      refine ⟨3612387144189073577449567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 77064259076033569652257429 3612387144189073577449567)
      ·
        refine ⟨5418580716283610366174351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3612387144189073577449567 5418580716283610366174351)
        ·
          refine ⟨8127871074425415549261527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5418580716283610366174351 8127871074425415549261527)
          ·
            refine ⟨12191806611638123323892291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8127871074425415549261527 12191806611638123323892291)
            ·
              refine ⟨18287709917457184985838437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12191806611638123323892291 18287709917457184985838437)
              ·
                refine ⟨3428945609523222184844707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18287709917457184985838437 3428945609523222184844707)
                ·
                  refine ⟨5143418414284833277267061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3428945609523222184844707 5143418414284833277267061)
                  ·
                    refine ⟨482195476339203119743787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5143418414284833277267061 482195476339203119743787)
                    ·
                      rfl

theorem cell23_2817217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 4, 1, 5].length) (baseStart_2817217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2817217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2817217 prefixEnd_2817217 := by exact prefixLift 2817217
  have htrace : WordTrace (prefixWord ++ tailWord_2817217) baseStart_2817217 baseEnd_2817217 := by
    simpa [prefixWord, tailWord_2817217, baseEnd_2817217] using wordTrace_append hprefix tailTrace_2817217
  have hstable : (prefixWord ++ tailWord_2817217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2817217).length < 2 ^ (prefixWord ++ tailWord_2817217).sum := by decide
  have hdescent : baseEnd_2817217 < baseStart_2817217 := by decide
  rcases family_descends (prefixWord ++ tailWord_2817217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2817223 : List Nat := [1, 1, 4, 1, 1, 1, 1, 2, 2, 6, 3]
def baseStart_2817223 : Nat := 118140960795 + 2817223 * 2 ^ 59
def prefixEnd_2817223 : Nat := 4983230072969 + 3 ^ 40 * 2817223 * 2
def baseEnd_2817223 : Nat := 1446589509901536335756333

theorem tailTrace_2817223 : CollatzResearch.WordTrace tailWord_2817223 prefixEnd_2817223 1446589509901536335756333 := by
  unfold tailWord_2817223
  simp only [CollatzResearch.WordTrace]
  refine ⟨102752564272689689227728323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68501709515126459485152215 102752564272689689227728323)
  ·
    refine ⟨154128846409034533841592485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102752564272689689227728323 154128846409034533841592485)
    ·
      refine ⟨28899158701693975095298591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 154128846409034533841592485 28899158701693975095298591)
      ·
        refine ⟨43348738052540962642947887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28899158701693975095298591 43348738052540962642947887)
        ·
          refine ⟨65023107078811443964421831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43348738052540962642947887 65023107078811443964421831)
          ·
            refine ⟨97534660618217165946632747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65023107078811443964421831 97534660618217165946632747)
            ·
              refine ⟨146301990927325748919949121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97534660618217165946632747 146301990927325748919949121)
              ·
                refine ⟨109726493195494311689961841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 146301990927325748919949121 109726493195494311689961841)
                ·
                  refine ⟨82294869896620733767471381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 109726493195494311689961841 82294869896620733767471381)
                  ·
                    refine ⟨3857572026404096895350221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 82294869896620733767471381 3857572026404096895350221)
                    ·
                      refine ⟨1446589509901536335756333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3857572026404096895350221 1446589509901536335756333)
                      ·
                        rfl

theorem cell23_2817223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 2, 2, 6, 3].length) (baseStart_2817223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2817223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2817223 prefixEnd_2817223 := by exact prefixLift 2817223
  have htrace : WordTrace (prefixWord ++ tailWord_2817223) baseStart_2817223 baseEnd_2817223 := by
    simpa [prefixWord, tailWord_2817223, baseEnd_2817223] using wordTrace_append hprefix tailTrace_2817223
  have hstable : (prefixWord ++ tailWord_2817223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2817223).length < 2 ^ (prefixWord ++ tailWord_2817223).sum := by decide
  have hdescent : baseEnd_2817223 < baseStart_2817223 := by decide
  rcases family_descends (prefixWord ++ tailWord_2817223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2817233 : List Nat := [1, 2, 2, 1, 2, 2, 1, 3, 3, 2, 4]
def baseStart_2817233 : Nat := 118140960795 + 2817233 * 2 ^ 59
def prefixEnd_2817233 : Nat := 4983230072969 + 3 ^ 40 * 2817233 * 2
def baseEnd_2817233 : Nat := 1446594644708081296631287

theorem tailTrace_2817233 : CollatzResearch.WordTrace tailWord_2817233 prefixEnd_2817233 1446594644708081296631287 := by
  unfold tailWord_2817233
  simp only [CollatzResearch.WordTrace]
  refine ⟨102752929002653460935592353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68501952668435640623728235 102752929002653460935592353)
  ·
    refine ⟨77064696751990095701694265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102752929002653460935592353 77064696751990095701694265)
    ·
      refine ⟨57798522563992571776270699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77064696751990095701694265 57798522563992571776270699)
      ·
        refine ⟨86697783845988857664406049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57798522563992571776270699 86697783845988857664406049)
        ·
          refine ⟨65023337884491643248304537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86697783845988857664406049 65023337884491643248304537)
          ·
            refine ⟨48767503413368732436228403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65023337884491643248304537 48767503413368732436228403)
            ·
              refine ⟨73151255120053098654342605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48767503413368732436228403 73151255120053098654342605)
              ·
                refine ⟨27431720670019911995378477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 73151255120053098654342605 27431720670019911995378477)
                ·
                  refine ⟨10286895251257466998266929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27431720670019911995378477 10286895251257466998266929)
                  ·
                    refine ⟨7715171438443100248700197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10286895251257466998266929 7715171438443100248700197)
                    ·
                      refine ⟨1446594644708081296631287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7715171438443100248700197 1446594644708081296631287)
                      ·
                        rfl

theorem cell23_2817233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 3, 3, 2, 4].length) (baseStart_2817233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2817233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2817233 prefixEnd_2817233 := by exact prefixLift 2817233
  have htrace : WordTrace (prefixWord ++ tailWord_2817233) baseStart_2817233 baseEnd_2817233 := by
    simpa [prefixWord, tailWord_2817233, baseEnd_2817233] using wordTrace_append hprefix tailTrace_2817233
  have hstable : (prefixWord ++ tailWord_2817233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2817233).length < 2 ^ (prefixWord ++ tailWord_2817233).sum := by decide
  have hdescent : baseEnd_2817233 < baseStart_2817233 := by decide
  rcases family_descends (prefixWord ++ tailWord_2817233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2817237 : List Nat := [1, 3, 2, 4, 1, 1, 2, 3, 1, 1, 4]
def baseStart_2817237 : Nat := 118140960795 + 2817237 * 2 ^ 59
def prefixEnd_2817237 : Nat := 4983230072969 + 3 ^ 40 * 2817237 * 2
def baseEnd_2817237 : Nat := 1446596698630699280981269

theorem tailTrace_2817237 : CollatzResearch.WordTrace tailWord_2817237 prefixEnd_2817237 1446596698630699280981269 := by
  unfold tailWord_2817237
  simp only [CollatzResearch.WordTrace]
  refine ⟨102753074894638969618737965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68502049929759313079158643 102753074894638969618737965)
  ·
    refine ⟨38532403085489613607026737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102753074894638969618737965 38532403085489613607026737)
    ·
      refine ⟨28899302314117210205270053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38532403085489613607026737 28899302314117210205270053)
      ·
        refine ⟨5418619183896976913488135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28899302314117210205270053 5418619183896976913488135)
        ·
          refine ⟨8127928775845465370232203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5418619183896976913488135 8127928775845465370232203)
          ·
            refine ⟨12191893163768198055348305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8127928775845465370232203 12191893163768198055348305)
            ·
              refine ⟨9143919872826148541511229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12191893163768198055348305 9143919872826148541511229)
              ·
                refine ⟨3428969952309805703066711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9143919872826148541511229 3428969952309805703066711)
                ·
                  refine ⟨5143454928464708554600067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3428969952309805703066711 5143454928464708554600067)
                  ·
                    refine ⟨7715182392697062831900101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5143454928464708554600067 7715182392697062831900101)
                    ·
                      refine ⟨1446596698630699280981269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7715182392697062831900101 1446596698630699280981269)
                      ·
                        rfl

theorem cell23_2817237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 2, 3, 1, 1, 4].length) (baseStart_2817237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2817237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2817237 prefixEnd_2817237 := by exact prefixLift 2817237
  have htrace : WordTrace (prefixWord ++ tailWord_2817237) baseStart_2817237 baseEnd_2817237 := by
    simpa [prefixWord, tailWord_2817237, baseEnd_2817237] using wordTrace_append hprefix tailTrace_2817237
  have hstable : (prefixWord ++ tailWord_2817237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2817237).length < 2 ^ (prefixWord ++ tailWord_2817237).sum := by decide
  have hdescent : baseEnd_2817237 < baseStart_2817237 := by decide
  rcases family_descends (prefixWord ++ tailWord_2817237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2817268 : List Nat := [2, 6, 1, 2, 1, 2, 1, 2, 1, 5]
def baseStart_2817268 : Nat := 118140960795 + 2817268 * 2 ^ 59
def prefixEnd_2817268 : Nat := 4983230072969 + 3 ^ 40 * 2817268 * 2
def baseEnd_2817268 : Nat := 482204205510329553231209

theorem tailTrace_2817268 : CollatzResearch.WordTrace tailWord_2817268 prefixEnd_2817268 482204205510329553231209 := by
  unfold tailWord_2817268
  simp only [CollatzResearch.WordTrace]
  refine ⟨51377102778763330956558229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68502803705017774608744305 51377102778763330956558229)
  ·
    refine ⟨2408301692754531138588667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 51377102778763330956558229 2408301692754531138588667)
    ·
      refine ⟨3612452539131796707883001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2408301692754531138588667 3612452539131796707883001)
      ·
        refine ⟨2709339404348847530912251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3612452539131796707883001 2709339404348847530912251)
        ·
          refine ⟨4064009106523271296368377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2709339404348847530912251 4064009106523271296368377)
          ·
            refine ⟨3048006829892453472276283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4064009106523271296368377 3048006829892453472276283)
            ·
              refine ⟨4572010244838680208414425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3048006829892453472276283 4572010244838680208414425)
              ·
                refine ⟨3429007683629010156310819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4572010244838680208414425 3429007683629010156310819)
                ·
                  refine ⟨5143511525443515234466229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3429007683629010156310819 5143511525443515234466229)
                  ·
                    refine ⟨482204205510329553231209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5143511525443515234466229 482204205510329553231209)
                    ·
                      rfl

theorem cell23_2817268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 1, 2, 1, 5].length) (baseStart_2817268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2817268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2817268 prefixEnd_2817268 := by exact prefixLift 2817268
  have htrace : WordTrace (prefixWord ++ tailWord_2817268) baseStart_2817268 baseEnd_2817268 := by
    simpa [prefixWord, tailWord_2817268, baseEnd_2817268] using wordTrace_append hprefix tailTrace_2817268
  have hstable : (prefixWord ++ tailWord_2817268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2817268).length < 2 ^ (prefixWord ++ tailWord_2817268).sum := by decide
  have hdescent : baseEnd_2817268 < baseStart_2817268 := by decide
  rcases family_descends (prefixWord ++ tailWord_2817268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2817304 : List Nat := [2, 1, 2, 3, 1, 4, 2, 2, 2, 1, 3]
def baseStart_2817304 : Nat := 118140960795 + 2817304 * 2 ^ 59
def prefixEnd_2817304 : Nat := 4983230072969 + 3 ^ 40 * 2817304 * 2
def baseEnd_2817304 : Nat := 1446631101834550518843461

theorem tailTrace_2817304 : CollatzResearch.WordTrace tailWord_2817304 prefixEnd_2817304 1446631101834550518843461 := by
  unfold tailWord_2817304
  simp only [CollatzResearch.WordTrace]
  refine ⟨51377759292698120030713483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68503679056930826707617977 51377759292698120030713483)
  ·
    refine ⟨77066638939047180046070225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51377759292698120030713483 77066638939047180046070225)
    ·
      refine ⟨57799979204285385034552669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77066638939047180046070225 57799979204285385034552669)
      ·
        refine ⟨21674992201607019387957251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57799979204285385034552669 21674992201607019387957251)
        ·
          refine ⟨32512488302410529081935877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21674992201607019387957251 32512488302410529081935877)
          ·
            refine ⟨6096091556701974202862977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32512488302410529081935877 6096091556701974202862977)
            ·
              refine ⟨4572068667526480652147233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6096091556701974202862977 4572068667526480652147233)
              ·
                refine ⟨3429051500644860489110425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4572068667526480652147233 3429051500644860489110425)
                ·
                  refine ⟨2571788625483645366832819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3429051500644860489110425 2571788625483645366832819)
                  ·
                    refine ⟨3857682938225468050249229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2571788625483645366832819 3857682938225468050249229)
                    ·
                      refine ⟨1446631101834550518843461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3857682938225468050249229 1446631101834550518843461)
                      ·
                        rfl

theorem cell23_2817304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 2, 2, 2, 1, 3].length) (baseStart_2817304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2817304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2817304 prefixEnd_2817304 := by exact prefixLift 2817304
  have htrace : WordTrace (prefixWord ++ tailWord_2817304) baseStart_2817304 baseEnd_2817304 := by
    simpa [prefixWord, tailWord_2817304, baseEnd_2817304] using wordTrace_append hprefix tailTrace_2817304
  have hstable : (prefixWord ++ tailWord_2817304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2817304).length < 2 ^ (prefixWord ++ tailWord_2817304).sum := by decide
  have hdescent : baseEnd_2817304 < baseStart_2817304 := by decide
  rcases family_descends (prefixWord ++ tailWord_2817304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2817320 : List Nat := [2, 1, 5, 1, 2, 1, 1, 1, 1, 8]
def baseStart_2817320 : Nat := 118140960795 + 2817320 * 2 ^ 59
def prefixEnd_2817320 : Nat := 4983230072969 + 3 ^ 40 * 2817320 * 2
def baseEnd_2817320 : Nat := 482213105841674152081129

theorem tailTrace_2817320 : CollatzResearch.WordTrace tailWord_2817320 prefixEnd_2817320 482213105841674152081129 := by
  unfold tailWord_2817320
  simp only [CollatzResearch.WordTrace]
  refine ⟨51378051076669137397004707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68504068102225516529339609 51378051076669137397004707)
  ·
    refine ⟨77067076615003706095507061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51378051076669137397004707 77067076615003706095507061)
    ·
      refine ⟨7225038432656597446453787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 77067076615003706095507061 7225038432656597446453787)
      ·
        refine ⟨10837557648984896169680681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7225038432656597446453787 10837557648984896169680681)
        ·
          refine ⟨8128168236738672127260511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10837557648984896169680681 8128168236738672127260511)
          ·
            refine ⟨12192252355108008190890767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8128168236738672127260511 12192252355108008190890767)
            ·
              refine ⟨18288378532662012286336151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12192252355108008190890767 18288378532662012286336151)
              ·
                refine ⟨27432567798993018429504227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18288378532662012286336151 27432567798993018429504227)
                ·
                  refine ⟨41148851698489527644256341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27432567798993018429504227 41148851698489527644256341)
                  ·
                    refine ⟨482213105841674152081129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 41148851698489527644256341 482213105841674152081129)
                    ·
                      rfl

theorem cell23_2817320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 1, 1, 8].length) (baseStart_2817320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2817320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2817320 prefixEnd_2817320 := by exact prefixLift 2817320
  have htrace : WordTrace (prefixWord ++ tailWord_2817320) baseStart_2817320 baseEnd_2817320 := by
    simpa [prefixWord, tailWord_2817320, baseEnd_2817320] using wordTrace_append hprefix tailTrace_2817320
  have hstable : (prefixWord ++ tailWord_2817320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2817320).length < 2 ^ (prefixWord ++ tailWord_2817320).sum := by decide
  have hdescent : baseEnd_2817320 < baseStart_2817320 := by decide
  rcases family_descends (prefixWord ++ tailWord_2817320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2817327 : List Nat := [1, 1, 2, 1, 2, 1, 3, 2, 6, 2, 2]
def baseStart_2817327 : Nat := 118140960795 + 2817327 * 2 ^ 59
def prefixEnd_2817327 : Nat := 4983230072969 + 3 ^ 40 * 2817327 * 2
def baseEnd_2817327 : Nat := 1446642911889603928855855

theorem tailTrace_2817327 : CollatzResearch.WordTrace tailWord_2817327 prefixEnd_2817327 1446642911889603928855855 := by
  unfold tailWord_2817327
  simp only [CollatzResearch.WordTrace]
  refine ⟨102756357464312914989514235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68504238309541943326342823 102756357464312914989514235)
  ·
    refine ⟨154134536196469372484271353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102756357464312914989514235 154134536196469372484271353)
    ·
      refine ⟨115600902147352029363203515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154134536196469372484271353 115600902147352029363203515)
      ·
        refine ⟨173401353221028044044805273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115600902147352029363203515 173401353221028044044805273)
        ·
          refine ⟨130051014915771033033603955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 173401353221028044044805273 130051014915771033033603955)
          ·
            refine ⟨195076522373656549550405933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130051014915771033033603955 195076522373656549550405933)
            ·
              refine ⟨73153695890121206081402225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 195076522373656549550405933 73153695890121206081402225)
              ·
                refine ⟨54865271917590904561051669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73153695890121206081402225 54865271917590904561051669)
                ·
                  refine ⟨2571809621137073651299297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 54865271917590904561051669 2571809621137073651299297)
                  ·
                    refine ⟨1928857215852805238474473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2571809621137073651299297 1928857215852805238474473)
                    ·
                      refine ⟨1446642911889603928855855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1928857215852805238474473 1446642911889603928855855)
                      ·
                        rfl

theorem cell23_2817327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 2, 6, 2, 2].length) (baseStart_2817327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2817327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2817327 prefixEnd_2817327 := by exact prefixLift 2817327
  have htrace : WordTrace (prefixWord ++ tailWord_2817327) baseStart_2817327 baseEnd_2817327 := by
    simpa [prefixWord, tailWord_2817327, baseEnd_2817327] using wordTrace_append hprefix tailTrace_2817327
  have hstable : (prefixWord ++ tailWord_2817327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2817327).length < 2 ^ (prefixWord ++ tailWord_2817327).sum := by decide
  have hdescent : baseEnd_2817327 < baseStart_2817327 := by decide
  rcases family_descends (prefixWord ++ tailWord_2817327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2817348 : List Nat := [2, 3, 4, 1, 1, 1, 4, 1, 1, 3, 2]
def baseStart_2817348 : Nat := 118140960795 + 2817348 * 2 ^ 59
def prefixEnd_2817348 : Nat := 4983230072969 + 3 ^ 40 * 2817348 * 2
def baseEnd_2817348 : Nat := 1446653694983348346693259

theorem tailTrace_2817348 : CollatzResearch.WordTrace tailWord_2817348 prefixEnd_2817348 1446653694983348346693259 := by
  unfold tailWord_2817348
  simp only [CollatzResearch.WordTrace]
  refine ⟨51378561698618417788014349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68504748931491223717352465 51378561698618417788014349)
  ·
    refine ⟨19266960636981906670505381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51378561698618417788014349 19266960636981906670505381)
    ·
      refine ⟨3612555119434107500719759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19266960636981906670505381 3612555119434107500719759)
      ·
        refine ⟨5418832679151161251079639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3612555119434107500719759 5418832679151161251079639)
        ·
          refine ⟨8128249018726741876619459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5418832679151161251079639 8128249018726741876619459)
          ·
            refine ⟨12192373528090112814929189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8128249018726741876619459 12192373528090112814929189)
            ·
              refine ⟨2286070036516896152799223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12192373528090112814929189 2286070036516896152799223)
              ·
                refine ⟨3429105054775344229198835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2286070036516896152799223 3429105054775344229198835)
                ·
                  refine ⟨5143657582163016343798253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3429105054775344229198835 5143657582163016343798253)
                  ·
                    refine ⟨1928871593311131128924345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5143657582163016343798253 1928871593311131128924345)
                    ·
                      refine ⟨1446653694983348346693259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1928871593311131128924345 1446653694983348346693259)
                      ·
                        rfl

theorem cell23_2817348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 4, 1, 1, 3, 2].length) (baseStart_2817348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2817348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2817348 prefixEnd_2817348 := by exact prefixLift 2817348
  have htrace : WordTrace (prefixWord ++ tailWord_2817348) baseStart_2817348 baseEnd_2817348 := by
    simpa [prefixWord, tailWord_2817348, baseEnd_2817348] using wordTrace_append hprefix tailTrace_2817348
  have hstable : (prefixWord ++ tailWord_2817348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2817348).length < 2 ^ (prefixWord ++ tailWord_2817348).sum := by decide
  have hdescent : baseEnd_2817348 < baseStart_2817348 := by decide
  rcases family_descends (prefixWord ++ tailWord_2817348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2817360 : List Nat := [2, 1, 1, 1, 1, 5, 1, 1, 4, 3, 3]
def baseStart_2817360 : Nat := 118140960795 + 2817360 * 2 ^ 59
def prefixEnd_2817360 : Nat := 4983230072969 + 3 ^ 40 * 2817360 * 2
def baseEnd_2817360 : Nat := 1446659856751202299743203

theorem tailTrace_2817360 : CollatzResearch.WordTrace tailWord_2817360 prefixEnd_2817360 1446659856751202299743203 := by
  unfold tailWord_2817360
  simp only [CollatzResearch.WordTrace]
  refine ⟨51378780536596680812732767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68505040715462241083643689 51378780536596680812732767)
  ·
    refine ⟨77068170804895021219099151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51378780536596680812732767 77068170804895021219099151)
    ·
      refine ⟨115602256207342531828648727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77068170804895021219099151 115602256207342531828648727)
      ·
        refine ⟨173403384311013797742973091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115602256207342531828648727 173403384311013797742973091)
        ·
          refine ⟨260105076466520696614459637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173403384311013797742973091 260105076466520696614459637)
          ·
            refine ⟨24384850918736315307605591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 260105076466520696614459637 24384850918736315307605591)
            ·
              refine ⟨36577276378104472961408387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24384850918736315307605591 36577276378104472961408387)
              ·
                refine ⟨54865914567156709442112581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36577276378104472961408387 54865914567156709442112581)
                ·
                  refine ⟨10287358981341883020396109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 54865914567156709442112581 10287358981341883020396109)
                  ·
                    refine ⟨3857759618003206132648541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10287358981341883020396109 3857759618003206132648541)
                    ·
                      refine ⟨1446659856751202299743203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3857759618003206132648541 1446659856751202299743203)
                      ·
                        rfl

theorem cell23_2817360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 1, 4, 3, 3].length) (baseStart_2817360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2817360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2817360 prefixEnd_2817360 := by exact prefixLift 2817360
  have htrace : WordTrace (prefixWord ++ tailWord_2817360) baseStart_2817360 baseEnd_2817360 := by
    simpa [prefixWord, tailWord_2817360, baseEnd_2817360] using wordTrace_append hprefix tailTrace_2817360
  have hstable : (prefixWord ++ tailWord_2817360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2817360).length < 2 ^ (prefixWord ++ tailWord_2817360).sum := by decide
  have hdescent : baseEnd_2817360 < baseStart_2817360 := by decide
  rcases family_descends (prefixWord ++ tailWord_2817360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2817367 : List Nat := [1, 1, 3, 2, 3, 2, 2, 4, 5]
def baseStart_2817367 : Nat := 118140960795 + 2817367 * 2 ^ 59
def prefixEnd_2817367 : Nat := 4983230072969 + 3 ^ 40 * 2817367 * 2
def baseEnd_2817367 : Nat := 160740383457309308039519

theorem tailTrace_2817367 : CollatzResearch.WordTrace tailWord_2817367 prefixEnd_2817367 160740383457309308039519 := by
  unfold tailWord_2817367
  simp only [CollatzResearch.WordTrace]
  refine ⟨102757816384168001820970355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68505210922778667880646903 102757816384168001820970355)
  ·
    refine ⟨154136724576252002731455533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102757816384168001820970355 154136724576252002731455533)
    ·
      refine ⟨57801271716094501024295825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 154136724576252002731455533 57801271716094501024295825)
      ·
        refine ⟨43350953787070875768221869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57801271716094501024295825 43350953787070875768221869)
        ·
          refine ⟨16256607670151578413083201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43350953787070875768221869 16256607670151578413083201)
          ·
            refine ⟨12192455752613683809812401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16256607670151578413083201 12192455752613683809812401)
            ·
              refine ⟨9144341814460262857359301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12192455752613683809812401 9144341814460262857359301)
              ·
                refine ⟨1714564090211299285754869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9144341814460262857359301 1714564090211299285754869)
                ·
                  refine ⟨160740383457309308039519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1714564090211299285754869 160740383457309308039519)
                  ·
                    rfl

theorem cell23_2817367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 2, 4, 5].length) (baseStart_2817367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2817367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2817367 prefixEnd_2817367 := by exact prefixLift 2817367
  have htrace : WordTrace (prefixWord ++ tailWord_2817367) baseStart_2817367 baseEnd_2817367 := by
    simpa [prefixWord, tailWord_2817367, baseEnd_2817367] using wordTrace_append hprefix tailTrace_2817367
  have hstable : (prefixWord ++ tailWord_2817367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2817367).length < 2 ^ (prefixWord ++ tailWord_2817367).sum := by decide
  have hdescent : baseEnd_2817367 < baseStart_2817367 := by decide
  rcases family_descends (prefixWord ++ tailWord_2817367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2817378 : List Nat := [3, 3, 2, 1, 1, 1, 5, 1, 2, 2, 2]
def baseStart_2817378 : Nat := 118140960795 + 2817378 * 2 ^ 59
def prefixEnd_2817378 : Nat := 4983230072969 + 3 ^ 40 * 2817378 * 2
def baseEnd_2817378 : Nat := 1446669099402983229318121

theorem tailTrace_2817378 : CollatzResearch.WordTrace tailWord_2817378 prefixEnd_2817378 1446669099402983229318121 := by
  unfold tailWord_2817378
  simp only [CollatzResearch.WordTrace]
  refine ⟨25689554396782037674905197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68505478391418767133080525 25689554396782037674905197)
  ·
    refine ⟨9633582898793264128089449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25689554396782037674905197 9633582898793264128089449)
    ·
      refine ⟨7225187174094948096067087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9633582898793264128089449 7225187174094948096067087)
      ·
        refine ⟨10837780761142422144100631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7225187174094948096067087 10837780761142422144100631)
        ·
          refine ⟨16256671141713633216150947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10837780761142422144100631 16256671141713633216150947)
          ·
            refine ⟨24385006712570449824226421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16256671141713633216150947 24385006712570449824226421)
            ·
              refine ⟨2286094379303479671021227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24385006712570449824226421 2286094379303479671021227)
              ·
                refine ⟨3429141568955219506531841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2286094379303479671021227 3429141568955219506531841)
                ·
                  refine ⟨2571856176716414629898881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3429141568955219506531841 2571856176716414629898881)
                  ·
                    refine ⟨1928892132537310972424161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2571856176716414629898881 1928892132537310972424161)
                    ·
                      refine ⟨1446669099402983229318121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1928892132537310972424161 1446669099402983229318121)
                      ·
                        rfl

theorem cell23_2817378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 5, 1, 2, 2, 2].length) (baseStart_2817378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2817378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2817378 prefixEnd_2817378 := by exact prefixLift 2817378
  have htrace : WordTrace (prefixWord ++ tailWord_2817378) baseStart_2817378 baseEnd_2817378 := by
    simpa [prefixWord, tailWord_2817378, baseEnd_2817378] using wordTrace_append hprefix tailTrace_2817378
  have hstable : (prefixWord ++ tailWord_2817378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2817378).length < 2 ^ (prefixWord ++ tailWord_2817378).sum := by decide
  have hdescent : baseEnd_2817378 < baseStart_2817378 := by decide
  rcases family_descends (prefixWord ++ tailWord_2817378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2817380 : List Nat := [2, 3, 1, 1, 3, 2, 1, 2, 1, 7]
def baseStart_2817380 : Nat := 118140960795 + 2817380 * 2 ^ 59
def prefixEnd_2817380 : Nat := 4983230072969 + 3 ^ 40 * 2817380 * 2
def baseEnd_2817380 : Nat := 482223375454764073831037

theorem tailTrace_2817380 : CollatzResearch.WordTrace tailWord_2817380 prefixEnd_2817380 482223375454764073831037 := by
  unfold tailWord_2817380
  simp only [CollatzResearch.WordTrace]
  refine ⟨51379145266560452520596797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68505527022080603360795729 51379145266560452520596797)
  ·
    refine ⟨19267179474960169695223799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51379145266560452520596797 19267179474960169695223799)
    ·
      refine ⟨28900769212440254542835699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19267179474960169695223799 28900769212440254542835699)
      ·
        refine ⟨43351153818660381814253549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28900769212440254542835699 43351153818660381814253549)
        ·
          refine ⟨16256682681997643180345081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43351153818660381814253549 16256682681997643180345081)
          ·
            refine ⟨12192512011498232385258811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16256682681997643180345081 12192512011498232385258811)
            ·
              refine ⟨18288768017247348577888217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12192512011498232385258811 18288768017247348577888217)
              ·
                refine ⟨13716576012935511433416163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18288768017247348577888217 13716576012935511433416163)
                ·
                  refine ⟨20574864019403267150124245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13716576012935511433416163 20574864019403267150124245)
                  ·
                    refine ⟨482223375454764073831037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 20574864019403267150124245 482223375454764073831037)
                    ·
                      rfl

theorem cell23_2817380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 2, 1, 7].length) (baseStart_2817380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2817380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2817380 prefixEnd_2817380 := by exact prefixLift 2817380
  have htrace : WordTrace (prefixWord ++ tailWord_2817380) baseStart_2817380 baseEnd_2817380 := by
    simpa [prefixWord, tailWord_2817380, baseEnd_2817380] using wordTrace_append hprefix tailTrace_2817380
  have hstable : (prefixWord ++ tailWord_2817380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2817380).length < 2 ^ (prefixWord ++ tailWord_2817380).sum := by decide
  have hdescent : baseEnd_2817380 < baseStart_2817380 := by decide
  rcases family_descends (prefixWord ++ tailWord_2817380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2817400 : List Nat := [2, 1, 2, 1, 1, 1, 1, 1, 8, 1, 4]
def baseStart_2817400 : Nat := 118140960795 + 2817400 * 2 ^ 59
def prefixEnd_2817400 : Nat := 4983230072969 + 3 ^ 40 * 2817400 * 2
def baseEnd_2817400 : Nat := 1446680395977382143243019

theorem tailTrace_2817400 : CollatzResearch.WordTrace tailWord_2817400 prefixEnd_2817400 1446680395977382143243019 := by
  unfold tailWord_2817400
  simp only [CollatzResearch.WordTrace]
  refine ⟨51379509996524224228460827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68506013328698965637947769 51379509996524224228460827)
  ·
    refine ⟨77069264994786336342691241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51379509996524224228460827 77069264994786336342691241)
    ·
      refine ⟨57801948746089752257018431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77069264994786336342691241 57801948746089752257018431)
      ·
        refine ⟨86702923119134628385527647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57801948746089752257018431 86702923119134628385527647)
        ·
          refine ⟨130054384678701942578291471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86702923119134628385527647 130054384678701942578291471)
          ·
            refine ⟨195081577018052913867437207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130054384678701942578291471 195081577018052913867437207)
            ·
              refine ⟨292622365527079370801155811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 195081577018052913867437207 292622365527079370801155811)
              ·
                refine ⟨438933548290619056201733717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 292622365527079370801155811 438933548290619056201733717)
                ·
                  refine ⟨5143752519030692064864067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 438933548290619056201733717 5143752519030692064864067)
                  ·
                    refine ⟨7715628778546038097296101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5143752519030692064864067 7715628778546038097296101)
                    ·
                      refine ⟨1446680395977382143243019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7715628778546038097296101 1446680395977382143243019)
                      ·
                        rfl

theorem cell23_2817400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 8, 1, 4].length) (baseStart_2817400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2817400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2817400 prefixEnd_2817400 := by exact prefixLift 2817400
  have htrace : WordTrace (prefixWord ++ tailWord_2817400) baseStart_2817400 baseEnd_2817400 := by
    simpa [prefixWord, tailWord_2817400, baseEnd_2817400] using wordTrace_append hprefix tailTrace_2817400
  have hstable : (prefixWord ++ tailWord_2817400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2817400).length < 2 ^ (prefixWord ++ tailWord_2817400).sum := by decide
  have hdescent : baseEnd_2817400 < baseStart_2817400 := by decide
  rcases family_descends (prefixWord ++ tailWord_2817400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2817501 : List Nat := [1, 4, 3, 1, 1, 3, 1, 2, 3, 1, 3]
def baseStart_2817501 : Nat := 118140960795 + 2817501 * 2 ^ 59
def prefixEnd_2817501 : Nat := 4983230072969 + 3 ^ 40 * 2817501 * 2
def baseEnd_2817501 : Nat := 1446732257523486248080055

theorem tailTrace_2817501 : CollatzResearch.WordTrace tailWord_2817501 prefixEnd_2817501 1446732257523486248080055 := by
  unfold tailWord_2817501
  simp only [CollatzResearch.WordTrace]
  refine ⟨102762703765682542706348357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68508469177121695137565571 102762703765682542706348357)
  ·
    refine ⟨19268006956065476757440317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 102762703765682542706348357 19268006956065476757440317)
    ·
      refine ⟨7225502608524553784040119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19268006956065476757440317 7225502608524553784040119)
      ·
        refine ⟨10838253912786830676060179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7225502608524553784040119 10838253912786830676060179)
        ·
          refine ⟨16257380869180246014090269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10838253912786830676060179 16257380869180246014090269)
          ·
            refine ⟨6096517825942592255283851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16257380869180246014090269 6096517825942592255283851)
            ·
              refine ⟨9144776738913888382925777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6096517825942592255283851 9144776738913888382925777)
              ·
                refine ⟨6858582554185416287194333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9144776738913888382925777 6858582554185416287194333)
                ·
                  refine ⟨2571968457819531107697875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6858582554185416287194333 2571968457819531107697875)
                  ·
                    refine ⟨3857952686729296661546813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2571968457819531107697875 3857952686729296661546813)
                    ·
                      refine ⟨1446732257523486248080055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3857952686729296661546813 1446732257523486248080055)
                      ·
                        rfl

theorem cell23_2817501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 1, 2, 3, 1, 3].length) (baseStart_2817501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2817501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2817501 prefixEnd_2817501 := by exact prefixLift 2817501
  have htrace : WordTrace (prefixWord ++ tailWord_2817501) baseStart_2817501 baseEnd_2817501 := by
    simpa [prefixWord, tailWord_2817501, baseEnd_2817501] using wordTrace_append hprefix tailTrace_2817501
  have hstable : (prefixWord ++ tailWord_2817501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2817501).length < 2 ^ (prefixWord ++ tailWord_2817501).sum := by decide
  have hdescent : baseEnd_2817501 < baseStart_2817501 := by decide
  rcases family_descends (prefixWord ++ tailWord_2817501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2817511 : List Nat := [1, 1, 5, 2, 1, 2, 3, 1, 2, 3, 2]
def baseStart_2817511 : Nat := 118140960795 + 2817511 * 2 ^ 59
def prefixEnd_2817511 : Nat := 4983230072969 + 3 ^ 40 * 2817511 * 2
def baseEnd_2817511 : Nat := 1446737392330031208955009

theorem tailTrace_2817511 : CollatzResearch.WordTrace tailWord_2817511 prefixEnd_2817511 1446737392330031208955009 := by
  unfold tailWord_2817511
  simp only [CollatzResearch.WordTrace]
  refine ⟨102763068495646314414212387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68508712330430876276141591 102763068495646314414212387)
  ·
    refine ⟨154144602743469471621318581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102763068495646314414212387 154144602743469471621318581)
    ·
      refine ⟨14451056507200262964498617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 154144602743469471621318581 14451056507200262964498617)
      ·
        refine ⟨10838292380400197223373963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14451056507200262964498617 10838292380400197223373963)
        ·
          refine ⟨16257438570600295835060945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10838292380400197223373963 16257438570600295835060945)
          ·
            refine ⟨12193078927950221876295709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16257438570600295835060945 12193078927950221876295709)
            ·
              refine ⟨4572404597981333203610891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12193078927950221876295709 4572404597981333203610891)
              ·
                refine ⟨6858606896971999805416337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4572404597981333203610891 6858606896971999805416337)
                ·
                  refine ⟨5143955172728999854062253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6858606896971999805416337 5143955172728999854062253)
                  ·
                    refine ⟨1928983189773374945273345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5143955172728999854062253 1928983189773374945273345)
                    ·
                      refine ⟨1446737392330031208955009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1928983189773374945273345 1446737392330031208955009)
                      ·
                        rfl

theorem cell23_2817511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 3, 1, 2, 3, 2].length) (baseStart_2817511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2817511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2817511 prefixEnd_2817511 := by exact prefixLift 2817511
  have htrace : WordTrace (prefixWord ++ tailWord_2817511) baseStart_2817511 baseEnd_2817511 := by
    simpa [prefixWord, tailWord_2817511, baseEnd_2817511] using wordTrace_append hprefix tailTrace_2817511
  have hstable : (prefixWord ++ tailWord_2817511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2817511).length < 2 ^ (prefixWord ++ tailWord_2817511).sum := by decide
  have hdescent : baseEnd_2817511 < baseStart_2817511 := by decide
  rcases family_descends (prefixWord ++ tailWord_2817511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2817518 : List Nat := [4, 1, 2, 1, 2, 1, 4, 3, 1, 1, 3]
def baseStart_2817518 : Nat := 118140960795 + 2817518 * 2 ^ 59
def prefixEnd_2817518 : Nat := 4983230072969 + 3 ^ 40 * 2817518 * 2
def baseEnd_2817518 : Nat := 1446740986694612681567477

theorem tailTrace_2817518 : CollatzResearch.WordTrace tailWord_2817518 prefixEnd_2817518 1446740986694612681567477 := by
  unfold tailWord_2817518
  simp only [CollatzResearch.WordTrace]
  refine ⟨12845415475827619326214651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68508882537747303073144805 12845415475827619326214651)
  ·
    refine ⟨19268123213741428989321977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12845415475827619326214651 19268123213741428989321977)
    ·
      refine ⟨14451092410306071741991483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19268123213741428989321977 14451092410306071741991483)
      ·
        refine ⟨21676638615459107612987225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14451092410306071741991483 21676638615459107612987225)
        ·
          refine ⟨16257478961594330709740419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21676638615459107612987225 16257478961594330709740419)
          ·
            refine ⟨24386218442391496064610629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16257478961594330709740419 24386218442391496064610629)
            ·
              refine ⟨4572415957948405512114493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24386218442391496064610629 4572415957948405512114493)
              ·
                refine ⟨1714655984230652067042935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4572415957948405512114493 1714655984230652067042935)
                ·
                  refine ⟨2571983976345978100564403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1714655984230652067042935 2571983976345978100564403)
                  ·
                    refine ⟨3857975964518967150846605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2571983976345978100564403 3857975964518967150846605)
                    ·
                      refine ⟨1446740986694612681567477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3857975964518967150846605 1446740986694612681567477)
                      ·
                        rfl

theorem cell23_2817518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 4, 3, 1, 1, 3].length) (baseStart_2817518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2817518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2817518 prefixEnd_2817518 := by exact prefixLift 2817518
  have htrace : WordTrace (prefixWord ++ tailWord_2817518) baseStart_2817518 baseEnd_2817518 := by
    simpa [prefixWord, tailWord_2817518, baseEnd_2817518] using wordTrace_append hprefix tailTrace_2817518
  have hstable : (prefixWord ++ tailWord_2817518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2817518).length < 2 ^ (prefixWord ++ tailWord_2817518).sum := by decide
  have hdescent : baseEnd_2817518 < baseStart_2817518 := by decide
  rcases family_descends (prefixWord ++ tailWord_2817518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2817521 : List Nat := [1, 2, 2, 2, 3, 4, 2, 1, 1, 5]
def baseStart_2817521 : Nat := 118140960795 + 2817521 * 2 ^ 59
def prefixEnd_2817521 : Nat := 4983230072969 + 3 ^ 40 * 2817521 * 2
def baseEnd_2817521 : Nat := 482247509045525389943321

theorem tailTrace_2817521 : CollatzResearch.WordTrace tailWord_2817521 prefixEnd_2817521 482247509045525389943321 := by
  unfold tailWord_2817521
  simp only [CollatzResearch.WordTrace]
  refine ⟨102763433225610086122076417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68508955483740057414717611 102763433225610086122076417)
  ·
    refine ⟨77072574919207564591557313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102763433225610086122076417 77072574919207564591557313)
    ·
      refine ⟨57804431189405673443667985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77072574919207564591557313 57804431189405673443667985)
      ·
        refine ⟨43353323392054255082750989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57804431189405673443667985 43353323392054255082750989)
        ·
          refine ⟨16257496272020345656031621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43353323392054255082750989 16257496272020345656031621)
          ·
            refine ⟨3048280551003814810505929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16257496272020345656031621 3048280551003814810505929)
            ·
              refine ⟨2286210413252861107879447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3048280551003814810505929 2286210413252861107879447)
              ·
                refine ⟨3429315619879291661819171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2286210413252861107879447 3429315619879291661819171)
                ·
                  refine ⟨5143973429818937492728757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3429315619879291661819171 5143973429818937492728757)
                  ·
                    refine ⟨482247509045525389943321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5143973429818937492728757 482247509045525389943321)
                    ·
                      rfl

theorem cell23_2817521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 2, 1, 1, 5].length) (baseStart_2817521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2817521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2817521 prefixEnd_2817521 := by exact prefixLift 2817521
  have htrace : WordTrace (prefixWord ++ tailWord_2817521) baseStart_2817521 baseEnd_2817521 := by
    simpa [prefixWord, tailWord_2817521, baseEnd_2817521] using wordTrace_append hprefix tailTrace_2817521
  have hstable : (prefixWord ++ tailWord_2817521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2817521).length < 2 ^ (prefixWord ++ tailWord_2817521).sum := by decide
  have hdescent : baseEnd_2817521 < baseStart_2817521 := by decide
  rcases family_descends (prefixWord ++ tailWord_2817521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2817527 : List Nat := [1, 1, 3, 1, 1, 1, 1, 4, 5, 2, 3]
def baseStart_2817527 : Nat := 118140960795 + 2817527 * 2 ^ 59
def prefixEnd_2817527 : Nat := 4983230072969 + 3 ^ 40 * 2817527 * 2
def baseEnd_2817527 : Nat := 1446745608020503146354935

theorem tailTrace_2817527 : CollatzResearch.WordTrace tailWord_2817527 prefixEnd_2817527 1446745608020503146354935 := by
  unfold tailWord_2817527
  simp only [CollatzResearch.WordTrace]
  refine ⟨102763652063588349146794835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68509101375725566097863223 102763652063588349146794835)
  ·
    refine ⟨154145478095382523720192253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102763652063588349146794835 154145478095382523720192253)
    ·
      refine ⟨57804554285768446395072095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 154145478095382523720192253 57804554285768446395072095)
      ·
        refine ⟨86706831428652669592608143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57804554285768446395072095 86706831428652669592608143)
        ·
          refine ⟨130060247142979004388912215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86706831428652669592608143 130060247142979004388912215)
          ·
            refine ⟨195090370714468506583368323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130060247142979004388912215 195090370714468506583368323)
            ·
              refine ⟨292635556071702759875052485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 195090370714468506583368323 292635556071702759875052485)
              ·
                refine ⟨54869166763444267476572341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 292635556071702759875052485 54869166763444267476572341)
                ·
                  refine ⟨5143984384072900075928657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 54869166763444267476572341 5143984384072900075928657)
                  ·
                    refine ⟨3857988288054675056946493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5143984384072900075928657 3857988288054675056946493)
                    ·
                      refine ⟨1446745608020503146354935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3857988288054675056946493 1446745608020503146354935)
                      ·
                        rfl

theorem cell23_2817527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 4, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 4, 5, 2, 3].length) (baseStart_2817527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2817527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2817527 prefixEnd_2817527 := by exact prefixLift 2817527
  have htrace : WordTrace (prefixWord ++ tailWord_2817527) baseStart_2817527 baseEnd_2817527 := by
    simpa [prefixWord, tailWord_2817527, baseEnd_2817527] using wordTrace_append hprefix tailTrace_2817527
  have hstable : (prefixWord ++ tailWord_2817527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2817527).length < 2 ^ (prefixWord ++ tailWord_2817527).sum := by decide
  have hdescent : baseEnd_2817527 < baseStart_2817527 := by decide
  rcases family_descends (prefixWord ++ tailWord_2817527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2817530 : List Nat := [3, 1, 1, 1, 1, 2, 14]
def baseStart_2817530 : Nat := 118140960795 + 2817530 * 2 ^ 59
def prefixEnd_2817530 : Nat := 4983230072969 + 3 ^ 40 * 2817530 * 2
def baseEnd_2817530 : Nat := 17861075906944032526141

theorem tailTrace_2817530 : CollatzResearch.WordTrace tailWord_2817530 prefixEnd_2817530 17861075906944032526141 := by
  unfold tailWord_2817530
  simp only [CollatzResearch.WordTrace]
  refine ⟨25690940370644370164788511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68509174321718320439436029 25690940370644370164788511)
  ·
    refine ⟨38536410555966555247182767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25690940370644370164788511 38536410555966555247182767)
    ·
      refine ⟨57804615833949832870774151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38536410555966555247182767 57804615833949832870774151)
      ·
        refine ⟨86706923750924749306161227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57804615833949832870774151 86706923750924749306161227)
        ·
          refine ⟨130060385626387123959241841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86706923750924749306161227 130060385626387123959241841)
          ·
            refine ⟨97545289219790342969431381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 130060385626387123959241841 97545289219790342969431381)
            ·
              refine ⟨17861075906944032526141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 14 97545289219790342969431381 17861075906944032526141)
              ·
                rfl

theorem cell23_2817530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 14].length) (baseStart_2817530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2817530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2817530 prefixEnd_2817530 := by exact prefixLift 2817530
  have htrace : WordTrace (prefixWord ++ tailWord_2817530) baseStart_2817530 baseEnd_2817530 := by
    simpa [prefixWord, tailWord_2817530, baseEnd_2817530] using wordTrace_append hprefix tailTrace_2817530
  have hstable : (prefixWord ++ tailWord_2817530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2817530).length < 2 ^ (prefixWord ++ tailWord_2817530).sum := by decide
  have hdescent : baseEnd_2817530 < baseStart_2817530 := by decide
  rcases family_descends (prefixWord ++ tailWord_2817530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2817584 : List Nat := [2, 1, 1, 1, 2, 3, 1, 2, 5, 3, 2]
def baseStart_2817584 : Nat := 118140960795 + 2817584 * 2 ^ 59
def prefixEnd_2817584 : Nat := 4983230072969 + 3 ^ 40 * 2817584 * 2
def baseEnd_2817584 : Nat := 1446774876417809423342173

theorem tailTrace_2817584 : CollatzResearch.WordTrace tailWord_2817584 prefixEnd_2817584 1446774876417809423342173 := by
  unfold tailWord_2817584
  simp only [CollatzResearch.WordTrace]
  refine ⟨51382865512190923940809903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68510487349587898587746537 51382865512190923940809903)
  ·
    refine ⟨77074298268286385911214855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51382865512190923940809903 77074298268286385911214855)
    ·
      refine ⟨115611447402429578866822283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77074298268286385911214855 115611447402429578866822283)
      ·
        refine ⟨173417171103644368300233425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115611447402429578866822283 173417171103644368300233425)
        ·
          refine ⟨130062878327733276225175069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 173417171103644368300233425 130062878327733276225175069)
          ·
            refine ⟨48773579372899978584440651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 130062878327733276225175069 48773579372899978584440651)
            ·
              refine ⟨73160369059349967876660977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48773579372899978584440651 73160369059349967876660977)
              ·
                refine ⟨54870276794512475907495733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73160369059349967876660977 54870276794512475907495733)
                ·
                  refine ⟨5144088449485544616327725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 54870276794512475907495733 5144088449485544616327725)
                  ·
                    refine ⟨1929033168557079231122897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5144088449485544616327725 1929033168557079231122897)
                    ·
                      refine ⟨1446774876417809423342173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1929033168557079231122897 1446774876417809423342173)
                      ·
                        rfl

theorem cell23_2817584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 2, 5, 3, 2].length) (baseStart_2817584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2817584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2817584 prefixEnd_2817584 := by exact prefixLift 2817584
  have htrace : WordTrace (prefixWord ++ tailWord_2817584) baseStart_2817584 baseEnd_2817584 := by
    simpa [prefixWord, tailWord_2817584, baseEnd_2817584] using wordTrace_append hprefix tailTrace_2817584
  have hstable : (prefixWord ++ tailWord_2817584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2817584).length < 2 ^ (prefixWord ++ tailWord_2817584).sum := by decide
  have hdescent : baseEnd_2817584 < baseStart_2817584 := by decide
  rcases family_descends (prefixWord ++ tailWord_2817584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2817601 : List Nat := [1, 2, 5, 1, 1, 1, 2, 2, 3, 3, 2]
def baseStart_2817601 : Nat := 118140960795 + 2817601 * 2 ^ 59
def prefixEnd_2817601 : Nat := 4983230072969 + 3 ^ 40 * 2817601 * 2
def baseEnd_2817601 : Nat := 1446783605588935856829595

theorem tailTrace_2817601 : CollatzResearch.WordTrace tailWord_2817601 prefixEnd_2817601 1446783605588935856829595 := by
  unfold tailWord_2817601
  simp only [CollatzResearch.WordTrace]
  refine ⟨102766351065320259784988657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68510900710213506523325771 102766351065320259784988657)
  ·
    refine ⟨77074763298990194838741493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102766351065320259784988657 77074763298990194838741493)
    ·
      refine ⟨7225759059280330766132015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 77074763298990194838741493 7225759059280330766132015)
      ·
        refine ⟨10838638588920496149198023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7225759059280330766132015 10838638588920496149198023)
        ·
          refine ⟨16257957883380744223797035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10838638588920496149198023 16257957883380744223797035)
          ·
            refine ⟨24386936825071116335695553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16257957883380744223797035 24386936825071116335695553)
            ·
              refine ⟨18290202618803337251771665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24386936825071116335695553 18290202618803337251771665)
              ·
                refine ⟨13717651964102502938828749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18290202618803337251771665 13717651964102502938828749)
                ·
                  refine ⟨5144119486538438602060781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13717651964102502938828749 5144119486538438602060781)
                  ·
                    refine ⟨1929044807451914475772793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5144119486538438602060781 1929044807451914475772793)
                    ·
                      refine ⟨1446783605588935856829595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1929044807451914475772793 1446783605588935856829595)
                      ·
                        rfl

theorem cell23_2817601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 2, 3, 3, 2].length) (baseStart_2817601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2817601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2817601 prefixEnd_2817601 := by exact prefixLift 2817601
  have htrace : WordTrace (prefixWord ++ tailWord_2817601) baseStart_2817601 baseEnd_2817601 := by
    simpa [prefixWord, tailWord_2817601, baseEnd_2817601] using wordTrace_append hprefix tailTrace_2817601
  have hstable : (prefixWord ++ tailWord_2817601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2817601).length < 2 ^ (prefixWord ++ tailWord_2817601).sum := by decide
  have hdescent : baseEnd_2817601 < baseStart_2817601 := by decide
  rcases family_descends (prefixWord ++ tailWord_2817601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2817617 : List Nat := [1, 2, 2, 1, 3, 2, 1, 1, 4, 1, 5]
def baseStart_2817617 : Nat := 118140960795 + 2817617 * 2 ^ 59
def prefixEnd_2817617 : Nat := 4983230072969 + 3 ^ 40 * 2817617 * 2
def baseEnd_2817617 : Nat := 1446791821279407794229521

theorem tailTrace_2817617 : CollatzResearch.WordTrace tailWord_2817617 prefixEnd_2817617 1446791821279407794229521 := by
  unfold tailWord_2817617
  simp only [CollatzResearch.WordTrace]
  refine ⟨102766934633262294517571105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68511289755508196345047403 102766934633262294517571105)
  ·
    refine ⟨77075200974946720888178329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102766934633262294517571105 77075200974946720888178329)
    ·
      refine ⟨57806400731210040666133747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77075200974946720888178329 57806400731210040666133747)
      ·
        refine ⟨86709601096815060999200621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57806400731210040666133747 86709601096815060999200621)
        ·
          refine ⟨32516100411305647874700233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86709601096815060999200621 32516100411305647874700233)
          ·
            refine ⟨24387075308479235906025175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32516100411305647874700233 24387075308479235906025175)
            ·
              refine ⟨36580612962718853859037763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24387075308479235906025175 36580612962718853859037763)
              ·
                refine ⟨54870919444078280788556645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36580612962718853859037763 54870919444078280788556645)
                ·
                  refine ⟨10288297395764677647854371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 54870919444078280788556645 10288297395764677647854371)
                  ·
                    refine ⟨15432446093647016471781557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10288297395764677647854371 15432446093647016471781557)
                    ·
                      refine ⟨1446791821279407794229521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15432446093647016471781557 1446791821279407794229521)
                      ·
                        rfl

theorem cell23_2817617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 1, 4, 1, 5].length) (baseStart_2817617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2817617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2817617 prefixEnd_2817617 := by exact prefixLift 2817617
  have htrace : WordTrace (prefixWord ++ tailWord_2817617) baseStart_2817617 baseEnd_2817617 := by
    simpa [prefixWord, tailWord_2817617, baseEnd_2817617] using wordTrace_append hprefix tailTrace_2817617
  have hstable : (prefixWord ++ tailWord_2817617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2817617).length < 2 ^ (prefixWord ++ tailWord_2817617).sum := by decide
  have hdescent : baseEnd_2817617 < baseStart_2817617 := by decide
  rcases family_descends (prefixWord ++ tailWord_2817617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2817618 : List Nat := [3, 2, 2, 1, 2, 2, 3, 2, 1, 3, 2]
def baseStart_2817618 : Nat := 118140960795 + 2817618 * 2 ^ 59
def prefixEnd_2817618 : Nat := 4983230072969 + 3 ^ 40 * 2817618 * 2
def baseEnd_2817618 : Nat := 1446792334760062290317017

theorem tailTrace_2817618 : CollatzResearch.WordTrace tailWord_2817618 prefixEnd_2817618 1446792334760062290317017 := by
  unfold tailWord_2817618
  simp only [CollatzResearch.WordTrace]
  refine ⟨25691742776564667922089377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68511314070839114458905005 25691742776564667922089377)
  ·
    refine ⟨19268807082423500941567033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25691742776564667922089377 19268807082423500941567033)
    ·
      refine ⟨14451605311817625706175275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19268807082423500941567033 14451605311817625706175275)
      ·
        refine ⟨21677407967726438559262913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14451605311817625706175275 21677407967726438559262913)
        ·
          refine ⟨16258055975794828919447185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21677407967726438559262913 16258055975794828919447185)
          ·
            refine ⟨12193541981846121689585389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16258055975794828919447185 12193541981846121689585389)
            ·
              refine ⟨4572578243192295633594521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12193541981846121689585389 4572578243192295633594521)
              ·
                refine ⟨3429433682394221725195891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4572578243192295633594521 3429433682394221725195891)
                ·
                  refine ⟨5144150523591332587793837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3429433682394221725195891 5144150523591332587793837)
                  ·
                    refine ⟨1929056446346749720422689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5144150523591332587793837 1929056446346749720422689)
                    ·
                      refine ⟨1446792334760062290317017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1929056446346749720422689 1446792334760062290317017)
                      ·
                        rfl

theorem cell23_2817618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 3, 2, 1, 3, 2].length) (baseStart_2817618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2817618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2817618 prefixEnd_2817618 := by exact prefixLift 2817618
  have htrace : WordTrace (prefixWord ++ tailWord_2817618) baseStart_2817618 baseEnd_2817618 := by
    simpa [prefixWord, tailWord_2817618, baseEnd_2817618] using wordTrace_append hprefix tailTrace_2817618
  have hstable : (prefixWord ++ tailWord_2817618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2817618).length < 2 ^ (prefixWord ++ tailWord_2817618).sum := by decide
  have hdescent : baseEnd_2817618 < baseStart_2817618 := by decide
  rcases family_descends (prefixWord ++ tailWord_2817618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2817648 : List Nat := [2, 1, 1, 1, 6, 1, 1, 4, 2, 2, 2]
def baseStart_2817648 : Nat := 118140960795 + 2817648 * 2 ^ 59
def prefixEnd_2817648 : Nat := 4983230072969 + 3 ^ 40 * 2817648 * 2
def baseEnd_2817648 : Nat := 1446807739179697172941879

theorem tailTrace_2817648 : CollatzResearch.WordTrace tailWord_2817648 prefixEnd_2817648 1446807739179697172941879 := by
  unfold tailWord_2817648
  simp only [CollatzResearch.WordTrace]
  refine ⟨51384032648074993405974799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68512043530766657874633065 51384032648074993405974799)
  ·
    refine ⟨77076048972112490108962199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51384032648074993405974799 77076048972112490108962199)
    ·
      refine ⟨115614073458168735163443299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77076048972112490108962199 115614073458168735163443299)
      ·
        refine ⟨173421110187253102745164949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115614073458168735163443299 173421110187253102745164949)
        ·
          refine ⟨8129114540027489191179607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 173421110187253102745164949 8129114540027489191179607)
          ·
            refine ⟨12193671810041233786769411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8129114540027489191179607 12193671810041233786769411)
            ·
              refine ⟨18290507715061850680154117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12193671810041233786769411 18290507715061850680154117)
              ·
                refine ⟨3429470196574097002528897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18290507715061850680154117 3429470196574097002528897)
                ·
                  refine ⟨2572102647430572751896673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3429470196574097002528897 2572102647430572751896673)
                  ·
                    refine ⟨1929076985572929563922505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2572102647430572751896673 1929076985572929563922505)
                    ·
                      refine ⟨1446807739179697172941879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1929076985572929563922505 1446807739179697172941879)
                      ·
                        rfl

theorem cell23_2817648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 4, 2, 2, 2].length) (baseStart_2817648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2817648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2817648 prefixEnd_2817648 := by exact prefixLift 2817648
  have htrace : WordTrace (prefixWord ++ tailWord_2817648) baseStart_2817648 baseEnd_2817648 := by
    simpa [prefixWord, tailWord_2817648, baseEnd_2817648] using wordTrace_append hprefix tailTrace_2817648
  have hstable : (prefixWord ++ tailWord_2817648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2817648).length < 2 ^ (prefixWord ++ tailWord_2817648).sum := by decide
  have hdescent : baseEnd_2817648 < baseStart_2817648 := by decide
  rcases family_descends (prefixWord ++ tailWord_2817648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2817664 : List Nat := [2, 1, 1, 2, 1, 4, 3, 1, 2, 3, 3]
def baseStart_2817664 : Nat := 118140960795 + 2817664 * 2 ^ 59
def prefixEnd_2817664 : Nat := 4983230072969 + 3 ^ 40 * 2817664 * 2
def baseEnd_2817664 : Nat := 1446815954870169110341805

theorem tailTrace_2817664 : CollatzResearch.WordTrace tailWord_2817664 prefixEnd_2817664 1446815954870169110341805 := by
  unfold tailWord_2817664
  simp only [CollatzResearch.WordTrace]
  refine ⟨51384324432046010772266023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68512432576061347696354697 51384324432046010772266023)
  ·
    refine ⟨77076486648069016158399035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51384324432046010772266023 77076486648069016158399035)
    ·
      refine ⟨115614729972103524237598553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77076486648069016158399035 115614729972103524237598553)
      ·
        refine ⟨86711047479077643178198915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115614729972103524237598553 86711047479077643178198915)
        ·
          refine ⟨130066571218616464767298373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86711047479077643178198915 130066571218616464767298373)
          ·
            refine ⟨24387482103490587143868445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 130066571218616464767298373 24387482103490587143868445)
            ·
              refine ⟨9145305788808970178950667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24387482103490587143868445 9145305788808970178950667)
              ·
                refine ⟨13717958683213455268426001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9145305788808970178950667 13717958683213455268426001)
                ·
                  refine ⟨10288469012410091451319501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13717958683213455268426001 10288469012410091451319501)
                  ·
                    refine ⟨3858175879653784294244813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10288469012410091451319501 3858175879653784294244813)
                    ·
                      refine ⟨1446815954870169110341805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3858175879653784294244813 1446815954870169110341805)
                      ·
                        rfl

theorem cell23_2817664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 3, 1, 2, 3, 3].length) (baseStart_2817664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2817664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2817664 prefixEnd_2817664 := by exact prefixLift 2817664
  have htrace : WordTrace (prefixWord ++ tailWord_2817664) baseStart_2817664 baseEnd_2817664 := by
    simpa [prefixWord, tailWord_2817664, baseEnd_2817664] using wordTrace_append hprefix tailTrace_2817664
  have hstable : (prefixWord ++ tailWord_2817664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2817664).length < 2 ^ (prefixWord ++ tailWord_2817664).sum := by decide
  have hdescent : baseEnd_2817664 < baseStart_2817664 := by decide
  rcases family_descends (prefixWord ++ tailWord_2817664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2817667 : List Nat := [1, 1, 1, 3, 3, 1, 1, 4, 1, 7]
def baseStart_2817667 : Nat := 118140960795 + 2817667 * 2 ^ 59
def prefixEnd_2817667 : Nat := 4983230072969 + 3 ^ 40 * 2817667 * 2
def baseEnd_2817667 : Nat := 482272498437377532868097

theorem tailTrace_2817667 : CollatzResearch.WordTrace tailWord_2817667 prefixEnd_2817667 482272498437377532868097 := by
  unfold tailWord_2817667
  simp only [CollatzResearch.WordTrace]
  refine ⟨102768758283081153056891255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68512505522054102037927503 102768758283081153056891255)
  ·
    refine ⟨154153137424621729585336883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102768758283081153056891255 154153137424621729585336883)
    ·
      refine ⟨231229706136932594378005325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154153137424621729585336883 231229706136932594378005325)
      ·
        refine ⟨86711139801349722891751997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 231229706136932594378005325 86711139801349722891751997)
        ·
          refine ⟨32516677425506146084406999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86711139801349722891751997 32516677425506146084406999)
          ·
            refine ⟨48775016138259219126610499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32516677425506146084406999 48775016138259219126610499)
            ·
              refine ⟨73162524207388828689915749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48775016138259219126610499 73162524207388828689915749)
              ·
                refine ⟨13717973288885405379359203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 73162524207388828689915749 13717973288885405379359203)
                ·
                  refine ⟨20576959933328108069038805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13717973288885405379359203 20576959933328108069038805)
                  ·
                    refine ⟨482272498437377532868097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 20576959933328108069038805 482272498437377532868097)
                    ·
                      rfl

theorem cell23_2817667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 4, 1, 7].length) (baseStart_2817667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2817667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2817667 prefixEnd_2817667 := by exact prefixLift 2817667
  have htrace : WordTrace (prefixWord ++ tailWord_2817667) baseStart_2817667 baseEnd_2817667 := by
    simpa [prefixWord, tailWord_2817667, baseEnd_2817667] using wordTrace_append hprefix tailTrace_2817667
  have hstable : (prefixWord ++ tailWord_2817667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2817667).length < 2 ^ (prefixWord ++ tailWord_2817667).sum := by decide
  have hdescent : baseEnd_2817667 < baseStart_2817667 := by decide
  rcases family_descends (prefixWord ++ tailWord_2817667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2817721 : List Nat := [1, 2, 1, 4, 1, 1, 4, 1, 2, 4, 2]
def baseStart_2817721 : Nat := 118140960795 + 2817721 * 2 ^ 59
def prefixEnd_2817721 : Nat := 4983230072969 + 3 ^ 40 * 2817721 * 2
def baseEnd_2817721 : Nat := 1446845223267475387329043

theorem tailTrace_2817721 : CollatzResearch.WordTrace tailWord_2817721 prefixEnd_2817721 1446845223267475387329043 := by
  unfold tailWord_2817721
  simp only [CollatzResearch.WordTrace]
  refine ⟨102770727824885520279357017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68513818549923680186238011 102770727824885520279357017)
  ·
    refine ⟨77078045868664140209517763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102770727824885520279357017 77078045868664140209517763)
    ·
      refine ⟨115617068802996210314276645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77078045868664140209517763 115617068802996210314276645)
      ·
        refine ⟨21678200400561789433926871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 115617068802996210314276645 21678200400561789433926871)
        ·
          refine ⟨32517300600842684150890307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21678200400561789433926871 32517300600842684150890307)
          ·
            refine ⟨48775950901264026226335461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32517300600842684150890307 48775950901264026226335461)
            ·
              refine ⟨9145490793987004917437899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48775950901264026226335461 9145490793987004917437899)
              ·
                refine ⟨13718236190980507376156849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9145490793987004917437899 13718236190980507376156849)
                ·
                  refine ⟨10288677143235380532117637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13718236190980507376156849 10288677143235380532117637)
                  ·
                    refine ⟨1929126964356633849772057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10288677143235380532117637 1929126964356633849772057)
                    ·
                      refine ⟨1446845223267475387329043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1929126964356633849772057 1446845223267475387329043)
                      ·
                        rfl

theorem cell23_2817721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 4, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 4, 1, 2, 4, 2].length) (baseStart_2817721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2817721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2817721 prefixEnd_2817721 := by exact prefixLift 2817721
  have htrace : WordTrace (prefixWord ++ tailWord_2817721) baseStart_2817721 baseEnd_2817721 := by
    simpa [prefixWord, tailWord_2817721, baseEnd_2817721] using wordTrace_append hprefix tailTrace_2817721
  have hstable : (prefixWord ++ tailWord_2817721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2817721).length < 2 ^ (prefixWord ++ tailWord_2817721).sum := by decide
  have hdescent : baseEnd_2817721 < baseStart_2817721 := by decide
  rcases family_descends (prefixWord ++ tailWord_2817721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2817737 : List Nat := [1, 2, 1, 1, 2, 1, 1, 1, 1, 3, 9]
def baseStart_2817737 : Nat := 118140960795 + 2817737 * 2 ^ 59
def prefixEnd_2817737 : Nat := 4983230072969 + 3 ^ 40 * 2817737 * 2
def baseEnd_2817737 : Nat := 1446853438957947324728969

theorem tailTrace_2817737 : CollatzResearch.WordTrace tailWord_2817737 prefixEnd_2817737 1446853438957947324728969 := by
  unfold tailWord_2817737
  simp only [CollatzResearch.WordTrace]
  refine ⟨102771311392827555011939465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68514207595218370007959643 102771311392827555011939465)
  ·
    refine ⟨77078483544620666258954599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102771311392827555011939465 77078483544620666258954599)
    ·
      refine ⟨115617725316930999388431899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77078483544620666258954599 115617725316930999388431899)
      ·
        refine ⟨173426587975396499082647849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115617725316930999388431899 173426587975396499082647849)
        ·
          refine ⟨130069940981547374311985887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 173426587975396499082647849 130069940981547374311985887)
          ·
            refine ⟨195104911472321061467978831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130069940981547374311985887 195104911472321061467978831)
            ·
              refine ⟨292657367208481592201968247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 195104911472321061467978831 292657367208481592201968247)
              ·
                refine ⟨438986050812722388302952371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 292657367208481592201968247 438986050812722388302952371)
                ·
                  refine ⟨658479076219083582454428557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 438986050812722388302952371 658479076219083582454428557)
                  ·
                    refine ⟨246929653582156343420410709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 658479076219083582454428557 246929653582156343420410709)
                    ·
                      refine ⟨1446853438957947324728969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 246929653582156343420410709 1446853438957947324728969)
                      ·
                        rfl

theorem cell23_2817737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 3, 9].length) (baseStart_2817737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2817737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2817737 prefixEnd_2817737 := by exact prefixLift 2817737
  have htrace : WordTrace (prefixWord ++ tailWord_2817737) baseStart_2817737 baseEnd_2817737 := by
    simpa [prefixWord, tailWord_2817737, baseEnd_2817737] using wordTrace_append hprefix tailTrace_2817737
  have hstable : (prefixWord ++ tailWord_2817737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2817737).length < 2 ^ (prefixWord ++ tailWord_2817737).sum := by decide
  have hdescent : baseEnd_2817737 < baseStart_2817737 := by decide
  rcases family_descends (prefixWord ++ tailWord_2817737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2817765 : List Nat := [1, 3, 1, 4, 1, 1, 5, 2, 1, 4]
def baseStart_2817765 : Nat := 118140960795 + 2817765 * 2 ^ 59
def prefixEnd_2817765 : Nat := 4983230072969 + 3 ^ 40 * 2817765 * 2
def baseEnd_2817765 : Nat := 482289272138757738392947

theorem tailTrace_2817765 : CollatzResearch.WordTrace tailWord_2817765 prefixEnd_2817765 482289272138757738392947 := by
  unfold tailWord_2817765
  simp only [CollatzResearch.WordTrace]
  refine ⟨102772332636726115793958749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68514888424484077195972499 102772332636726115793958749)
  ·
    refine ⟨38539624738772293422734531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102772332636726115793958749 38539624738772293422734531)
    ·
      refine ⟨57809437108158440134101797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38539624738772293422734531 57809437108158440134101797)
      ·
        refine ⟨10839269457779707525144087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57809437108158440134101797 10839269457779707525144087)
        ·
          refine ⟨16258904186669561287716131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10839269457779707525144087 16258904186669561287716131)
          ·
            refine ⟨24388356280004341931574197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16258904186669561287716131 24388356280004341931574197)
            ·
              refine ⟨2286408401250407056085081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24388356280004341931574197 2286408401250407056085081)
              ·
                refine ⟨1714806300937805292063811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2286408401250407056085081 1714806300937805292063811)
                ·
                  refine ⟨2572209451406707938095717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1714806300937805292063811 2572209451406707938095717)
                  ·
                    refine ⟨482289272138757738392947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2572209451406707938095717 482289272138757738392947)
                    ·
                      rfl

theorem cell23_2817765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 5, 2, 1, 4].length) (baseStart_2817765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2817765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2817765 prefixEnd_2817765 := by exact prefixLift 2817765
  have htrace : WordTrace (prefixWord ++ tailWord_2817765) baseStart_2817765 baseEnd_2817765 := by
    simpa [prefixWord, tailWord_2817765, baseEnd_2817765] using wordTrace_append hprefix tailTrace_2817765
  have hstable : (prefixWord ++ tailWord_2817765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2817765).length < 2 ^ (prefixWord ++ tailWord_2817765).sum := by decide
  have hdescent : baseEnd_2817765 < baseStart_2817765 := by decide
  rcases family_descends (prefixWord ++ tailWord_2817765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2817791 : List Nat := [1, 1, 2, 2, 1, 3, 5, 2, 1, 5]
def baseStart_2817791 : Nat := 118140960795 + 2817791 * 2 ^ 59
def prefixEnd_2817791 : Nat := 4983230072969 + 3 ^ 40 * 2817791 * 2
def baseEnd_2817791 : Nat := 482293722304430037817907

theorem tailTrace_2817791 : CollatzResearch.WordTrace tailWord_2817791 prefixEnd_2817791 482293722304430037817907 := by
  unfold tailWord_2817791
  simp only [CollatzResearch.WordTrace]
  refine ⟨102773280934631922234405227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68515520623087948156270151 102773280934631922234405227)
  ·
    refine ⟨154159921401947883351607841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102773280934631922234405227 154159921401947883351607841)
    ·
      refine ⟨115619941051460912513705881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154159921401947883351607841 115619941051460912513705881)
      ·
        refine ⟨86714955788595684385279411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115619941051460912513705881 86714955788595684385279411)
        ·
          refine ⟨130072433682893526577919117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86714955788595684385279411 130072433682893526577919117)
          ·
            refine ⟨48777162631085072466719669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 130072433682893526577919117 48777162631085072466719669)
            ·
              refine ⟨4572858996664225543754969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 48777162631085072466719669 4572858996664225543754969)
              ·
                refine ⟨3429644247498169157816227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4572858996664225543754969 3429644247498169157816227)
                ·
                  refine ⟨5144466371247253736724341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3429644247498169157816227 5144466371247253736724341)
                  ·
                    refine ⟨482293722304430037817907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5144466371247253736724341 482293722304430037817907)
                    ·
                      rfl

theorem cell23_2817791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 5, 2, 1, 5].length) (baseStart_2817791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2817791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2817791 prefixEnd_2817791 := by exact prefixLift 2817791
  have htrace : WordTrace (prefixWord ++ tailWord_2817791) baseStart_2817791 baseEnd_2817791 := by
    simpa [prefixWord, tailWord_2817791, baseEnd_2817791] using wordTrace_append hprefix tailTrace_2817791
  have hstable : (prefixWord ++ tailWord_2817791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2817791).length < 2 ^ (prefixWord ++ tailWord_2817791).sum := by decide
  have hdescent : baseEnd_2817791 < baseStart_2817791 := by decide
  rcases family_descends (prefixWord ++ tailWord_2817791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2817804 : List Nat := [2, 2, 1, 2, 2, 1, 3, 1, 3, 6]
def baseStart_2817804 : Nat := 118140960795 + 2817804 * 2 ^ 59
def prefixEnd_2817804 : Nat := 4983230072969 + 3 ^ 40 * 2817804 * 2
def baseEnd_2817804 : Nat := 482295947387266187530387

theorem tailTrace_2817804 : CollatzResearch.WordTrace tailWord_2817804 prefixEnd_2817804 482295947387266187530387 := by
  unfold tailWord_2817804
  simp only [CollatzResearch.WordTrace]
  refine ⟨51386877541792412727314233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68515836722389883636418977 51386877541792412727314233)
  ·
    refine ⟨38540158156344309545485675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51386877541792412727314233 38540158156344309545485675)
    ·
      refine ⟨57810237234516464318228513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38540158156344309545485675 57810237234516464318228513)
      ·
        refine ⟨43357677925887348238671385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57810237234516464318228513 43357677925887348238671385)
        ·
          refine ⟨32518258444415511179003539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43357677925887348238671385 32518258444415511179003539)
          ·
            refine ⟨48777387666623266768505309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32518258444415511179003539 48777387666623266768505309)
            ·
              refine ⟨18291520374983725038189491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48777387666623266768505309 18291520374983725038189491)
              ·
                refine ⟨27437280562475587557284237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18291520374983725038189491 27437280562475587557284237)
                ·
                  refine ⟨10288980210928345333981589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27437280562475587557284237 10288980210928345333981589)
                  ·
                    refine ⟨482295947387266187530387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10288980210928345333981589 482295947387266187530387)
                    ·
                      rfl

theorem cell23_2817804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 1, 3, 6].length) (baseStart_2817804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2817804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2817804 prefixEnd_2817804 := by exact prefixLift 2817804
  have htrace : WordTrace (prefixWord ++ tailWord_2817804) baseStart_2817804 baseEnd_2817804 := by
    simpa [prefixWord, tailWord_2817804, baseEnd_2817804] using wordTrace_append hprefix tailTrace_2817804
  have hstable : (prefixWord ++ tailWord_2817804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2817804).length < 2 ^ (prefixWord ++ tailWord_2817804).sum := by decide
  have hdescent : baseEnd_2817804 < baseStart_2817804 := by decide
  rcases family_descends (prefixWord ++ tailWord_2817804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2817812 : List Nat := [2, 4, 4, 1, 1, 1, 2, 2, 6]
def baseStart_2817812 : Nat := 118140960795 + 2817812 * 2 ^ 59
def prefixEnd_2817812 : Nat := 4983230072969 + 3 ^ 40 * 2817812 * 2
def baseEnd_2817812 : Nat := 160765772223003836810125

theorem tailTrace_2817812 : CollatzResearch.WordTrace tailWord_2817812 prefixEnd_2817812 160765772223003836810125 := by
  unfold tailWord_2817812
  simp only [CollatzResearch.WordTrace]
  refine ⟨51387023433777921410459845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68516031245037228547279793 51387023433777921410459845)
  ·
    refine ⟨9635066893833360264461221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51387023433777921410459845 9635066893833360264461221)
    ·
      refine ⟨1806575042593755049586479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9635066893833360264461221 1806575042593755049586479)
      ·
        refine ⟨2709862563890632574379719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1806575042593755049586479 2709862563890632574379719)
        ·
          refine ⟨4064793845835948861569579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2709862563890632574379719 4064793845835948861569579)
          ·
            refine ⟨6097190768753923292354369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4064793845835948861569579 6097190768753923292354369)
            ·
              refine ⟨4572893076565442469265777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6097190768753923292354369 4572893076565442469265777)
              ·
                refine ⟨3429669807424081851949333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4572893076565442469265777 3429669807424081851949333)
                ·
                  refine ⟨160765772223003836810125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3429669807424081851949333 160765772223003836810125)
                  ·
                    rfl

theorem cell23_2817812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 2, 2, 6].length) (baseStart_2817812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2817812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2817812 prefixEnd_2817812 := by exact prefixLift 2817812
  have htrace : WordTrace (prefixWord ++ tailWord_2817812) baseStart_2817812 baseEnd_2817812 := by
    simpa [prefixWord, tailWord_2817812, baseEnd_2817812] using wordTrace_append hprefix tailTrace_2817812
  have hstable : (prefixWord ++ tailWord_2817812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2817812).length < 2 ^ (prefixWord ++ tailWord_2817812).sum := by decide
  have hdescent : baseEnd_2817812 < baseStart_2817812 := by decide
  rcases family_descends (prefixWord ++ tailWord_2817812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2817841 : List Nat := [1, 2, 2, 3, 2, 2, 1, 3, 1, 2, 4]
def baseStart_2817841 : Nat := 118140960795 + 2817841 * 2 ^ 59
def prefixEnd_2817841 : Nat := 4983230072969 + 3 ^ 40 * 2817841 * 2
def baseEnd_2817841 : Nat := 1446906840946014917828491

theorem tailTrace_2817841 : CollatzResearch.WordTrace tailWord_2817841 prefixEnd_2817841 1446906840946014917828491 := by
  unfold tailWord_2817841
  simp only [CollatzResearch.WordTrace]
  refine ⟨102775104584450780773725377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68516736389633853849150251 102775104584450780773725377)
  ·
    refine ⟨77081328438338085580294033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102775104584450780773725377 77081328438338085580294033)
    ·
      refine ⟨57810996328753564185220525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77081328438338085580294033 57810996328753564185220525)
      ·
        refine ⟨21679123623282586569457697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57810996328753564185220525 21679123623282586569457697)
        ·
          refine ⟨16259342717461939927093273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21679123623282586569457697 16259342717461939927093273)
          ·
            refine ⟨12194507038096454945319955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16259342717461939927093273 12194507038096454945319955)
            ·
              refine ⟨18291760557144682417979933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12194507038096454945319955 18291760557144682417979933)
              ·
                refine ⟨6859410208929255906742475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18291760557144682417979933 6859410208929255906742475)
                ·
                  refine ⟨10289115313393883860113713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6859410208929255906742475 10289115313393883860113713)
                  ·
                    refine ⟨7716836485045412895085285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10289115313393883860113713 7716836485045412895085285)
                    ·
                      refine ⟨1446906840946014917828491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7716836485045412895085285 1446906840946014917828491)
                      ·
                        rfl

theorem cell23_2817841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 3, 1, 2, 4].length) (baseStart_2817841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2817841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2817841 prefixEnd_2817841 := by exact prefixLift 2817841
  have htrace : WordTrace (prefixWord ++ tailWord_2817841) baseStart_2817841 baseEnd_2817841 := by
    simpa [prefixWord, tailWord_2817841, baseEnd_2817841] using wordTrace_append hprefix tailTrace_2817841
  have hstable : (prefixWord ++ tailWord_2817841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2817841).length < 2 ^ (prefixWord ++ tailWord_2817841).sum := by decide
  have hdescent : baseEnd_2817841 < baseStart_2817841 := by decide
  rcases family_descends (prefixWord ++ tailWord_2817841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2817849 : List Nat := [1, 2, 1, 7, 2, 1, 1, 1, 2, 3, 2]
def baseStart_2817849 : Nat := 118140960795 + 2817849 * 2 ^ 59
def prefixEnd_2817849 : Nat := 4983230072969 + 3 ^ 40 * 2817849 * 2
def baseEnd_2817849 : Nat := 1446910948791250886528455

theorem tailTrace_2817849 : CollatzResearch.WordTrace tailWord_2817849 prefixEnd_2817849 1446910948791250886528455 := by
  unfold tailWord_2817849
  simp only [CollatzResearch.WordTrace]
  refine ⟨102775396368421798140016601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68516930912281198760011067 102775396368421798140016601)
  ·
    refine ⟨77081547276316348605012451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102775396368421798140016601 77081547276316348605012451)
    ·
      refine ⟨115622320914474522907518677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77081547276316348605012451 115622320914474522907518677)
      ·
        refine ⟨2709898146432996630644969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 115622320914474522907518677 2709898146432996630644969)
        ·
          refine ⟨2032423609824747472983727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2709898146432996630644969 2032423609824747472983727)
          ·
            refine ⟨3048635414737121209475591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2032423609824747472983727 3048635414737121209475591)
            ·
              refine ⟨4572953122105681814213387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3048635414737121209475591 4572953122105681814213387)
              ·
                refine ⟨6859429683158522721320081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4572953122105681814213387 6859429683158522721320081)
                ·
                  refine ⟨5144572262368892040990061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6859429683158522721320081 5144572262368892040990061)
                  ·
                    refine ⟨1929214598388334515371273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5144572262368892040990061 1929214598388334515371273)
                    ·
                      refine ⟨1446910948791250886528455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1929214598388334515371273 1446910948791250886528455)
                      ·
                        rfl

theorem cell23_2817849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 1, 1, 2, 3, 2].length) (baseStart_2817849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2817849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2817849 prefixEnd_2817849 := by exact prefixLift 2817849
  have htrace : WordTrace (prefixWord ++ tailWord_2817849) baseStart_2817849 baseEnd_2817849 := by
    simpa [prefixWord, tailWord_2817849, baseEnd_2817849] using wordTrace_append hprefix tailTrace_2817849
  have hstable : (prefixWord ++ tailWord_2817849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2817849).length < 2 ^ (prefixWord ++ tailWord_2817849).sum := by decide
  have hdescent : baseEnd_2817849 < baseStart_2817849 := by decide
  rcases family_descends (prefixWord ++ tailWord_2817849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2817861 : List Nat := [1, 3, 1, 1, 1, 2, 3, 4, 1, 3, 3]
def baseStart_2817861 : Nat := 118140960795 + 2817861 * 2 ^ 59
def prefixEnd_2817861 : Nat := 4983230072969 + 3 ^ 40 * 2817861 * 2
def baseEnd_2817861 : Nat := 1446917110559104839578399

theorem tailTrace_2817861 : CollatzResearch.WordTrace tailWord_2817861 prefixEnd_2817861 1446917110559104839578399 := by
  unfold tailWord_2817861
  simp only [CollatzResearch.WordTrace]
  refine ⟨102775834044378324189453437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68517222696252216126302291 102775834044378324189453437)
  ·
    refine ⟨38540937766641871571045039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102775834044378324189453437 38540937766641871571045039)
    ·
      refine ⟨57811406649962807356567559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38540937766641871571045039 57811406649962807356567559)
      ·
        refine ⟨86717109974944211034851339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57811406649962807356567559 86717109974944211034851339)
        ·
          refine ⟨130075664962416316552277009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86717109974944211034851339 130075664962416316552277009)
          ·
            refine ⟨97556748721812237414207757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 130075664962416316552277009 97556748721812237414207757)
            ·
              refine ⟨36583780770679589030327909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 97556748721812237414207757 36583780770679589030327909)
              ·
                refine ⟨6859458894502422943186483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36583780770679589030327909 6859458894502422943186483)
                ·
                  refine ⟨10289188341753634414779725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6859458894502422943186483 10289188341753634414779725)
                  ·
                    refine ⟨3858445628157612905542397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10289188341753634414779725 3858445628157612905542397)
                    ·
                      refine ⟨1446917110559104839578399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3858445628157612905542397 1446917110559104839578399)
                      ·
                        rfl

theorem cell23_2817861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 4, 1, 3, 3].length) (baseStart_2817861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2817861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2817861 prefixEnd_2817861 := by exact prefixLift 2817861
  have htrace : WordTrace (prefixWord ++ tailWord_2817861) baseStart_2817861 baseEnd_2817861 := by
    simpa [prefixWord, tailWord_2817861, baseEnd_2817861] using wordTrace_append hprefix tailTrace_2817861
  have hstable : (prefixWord ++ tailWord_2817861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2817861).length < 2 ^ (prefixWord ++ tailWord_2817861).sum := by decide
  have hdescent : baseEnd_2817861 < baseStart_2817861 := by decide
  rcases family_descends (prefixWord ++ tailWord_2817861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2817862 : List Nat := [6, 1, 1, 2, 1, 2, 1, 3, 1, 1, 4]
def baseStart_2817862 : Nat := 118140960795 + 2817862 * 2 ^ 59
def prefixEnd_2817862 : Nat := 4983230072969 + 3 ^ 40 * 2817862 * 2
def baseEnd_2817862 : Nat := 1446917624039759335665895

theorem tailTrace_2817862 : CollatzResearch.WordTrace tailWord_2817862 prefixEnd_2817862 1446917624039759335665895 := by
  unfold tailWord_2817862
  simp only [CollatzResearch.WordTrace]
  refine ⟨3211745953667959417507495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 68517247011583134240159893 3211745953667959417507495)
  ·
    refine ⟨4817618930501939126261243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3211745953667959417507495 4817618930501939126261243)
    ·
      refine ⟨7226428395752908689391865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4817618930501939126261243 7226428395752908689391865)
      ·
        refine ⟨5419821296814681517043899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7226428395752908689391865 5419821296814681517043899)
        ·
          refine ⟨8129731945222022275565849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5419821296814681517043899 8129731945222022275565849)
          ·
            refine ⟨6097298958916516706674387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8129731945222022275565849 6097298958916516706674387)
            ·
              refine ⟨9145948438374775060011581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6097298958916516706674387 9145948438374775060011581)
              ·
                refine ⟨3429730664390540647504343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9145948438374775060011581 3429730664390540647504343)
                ·
                  refine ⟨5144595996585810971256515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3429730664390540647504343 5144595996585810971256515)
                  ·
                    refine ⟨7716893994878716456884773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5144595996585810971256515 7716893994878716456884773)
                    ·
                      refine ⟨1446917624039759335665895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7716893994878716456884773 1446917624039759335665895)
                      ·
                        rfl

theorem cell23_2817862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 1, 3, 1, 1, 4].length) (baseStart_2817862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2817862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2817862 prefixEnd_2817862 := by exact prefixLift 2817862
  have htrace : WordTrace (prefixWord ++ tailWord_2817862) baseStart_2817862 baseEnd_2817862 := by
    simpa [prefixWord, tailWord_2817862, baseEnd_2817862] using wordTrace_append hprefix tailTrace_2817862
  have hstable : (prefixWord ++ tailWord_2817862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2817862).length < 2 ^ (prefixWord ++ tailWord_2817862).sum := by decide
  have hdescent : baseEnd_2817862 < baseStart_2817862 := by decide
  rcases family_descends (prefixWord ++ tailWord_2817862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2817901 : List Nat := [1, 5, 1, 1, 1, 1, 2, 2, 2, 3, 4]
def baseStart_2817901 : Nat := 118140960795 + 2817901 * 2 ^ 59
def prefixEnd_2817901 : Nat := 4983230072969 + 3 ^ 40 * 2817901 * 2
def baseEnd_2817901 : Nat := 1446937649785284683078215

theorem tailTrace_2817901 : CollatzResearch.WordTrace tailWord_2817901 prefixEnd_2817901 1446937649785284683078215 := by
  unfold tailWord_2817901
  simp only [CollatzResearch.WordTrace]
  refine ⟨102777292964233411020909557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68518195309488940680606371 102777292964233411020909557)
  ·
    refine ⟨9635371215396882283210271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 102777292964233411020909557 9635371215396882283210271)
    ·
      refine ⟨14453056823095323424815407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9635371215396882283210271 14453056823095323424815407)
      ·
        refine ⟨21679585234642985137223111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14453056823095323424815407 21679585234642985137223111)
        ·
          refine ⟨32519377851964477705834667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21679585234642985137223111 32519377851964477705834667)
          ·
            refine ⟨48779066777946716558752001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32519377851964477705834667 48779066777946716558752001)
            ·
              refine ⟨36584300083460037419064001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48779066777946716558752001 36584300083460037419064001)
              ·
                refine ⟨27438225062595028064298001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36584300083460037419064001 27438225062595028064298001)
                ·
                  refine ⟨20578668796946271048223501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27438225062595028064298001 20578668796946271048223501)
                  ·
                    refine ⟨7717000798854851643083813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20578668796946271048223501 7717000798854851643083813)
                    ·
                      refine ⟨1446937649785284683078215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7717000798854851643083813 1446937649785284683078215)
                      ·
                        rfl

theorem cell23_2817901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 2, 2, 3, 4].length) (baseStart_2817901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2817901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2817901 prefixEnd_2817901 := by exact prefixLift 2817901
  have htrace : WordTrace (prefixWord ++ tailWord_2817901) baseStart_2817901 baseEnd_2817901 := by
    simpa [prefixWord, tailWord_2817901, baseEnd_2817901] using wordTrace_append hprefix tailTrace_2817901
  have hstable : (prefixWord ++ tailWord_2817901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2817901).length < 2 ^ (prefixWord ++ tailWord_2817901).sum := by decide
  have hdescent : baseEnd_2817901 < baseStart_2817901 := by decide
  rcases family_descends (prefixWord ++ tailWord_2817901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2817905 : List Nat := [1, 2, 2, 2, 1, 3, 4, 2, 1, 3, 2]
def baseStart_2817905 : Nat := 118140960795 + 2817905 * 2 ^ 59
def prefixEnd_2817905 : Nat := 4983230072969 + 3 ^ 40 * 2817905 * 2
def baseEnd_2817905 : Nat := 1446939703707902667428197

theorem tailTrace_2817905 : CollatzResearch.WordTrace tailWord_2817905 prefixEnd_2817905 1446939703707902667428197 := by
  unfold tailWord_2817905
  simp only [CollatzResearch.WordTrace]
  refine ⟨102777438856218919704055169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68518292570812613136036779 102777438856218919704055169)
  ·
    refine ⟨77083079142164189778041377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102777438856218919704055169 77083079142164189778041377)
    ·
      refine ⟨57812309356623142333531033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77083079142164189778041377 57812309356623142333531033)
      ·
        refine ⟨43359232017467356750148275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57812309356623142333531033 43359232017467356750148275)
        ·
          refine ⟨65038848026201035125222413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43359232017467356750148275 65038848026201035125222413)
          ·
            refine ⟨24389568009825388171958405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65038848026201035125222413 24389568009825388171958405)
            ·
              refine ⟨4573044001842260282242201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24389568009825388171958405 4573044001842260282242201)
              ·
                refine ⟨3429783001381695211681651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4573044001842260282242201 3429783001381695211681651)
                ·
                  refine ⟨5144674502072542817522477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3429783001381695211681651 5144674502072542817522477)
                  ·
                    refine ⟨1929252938277203556570929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5144674502072542817522477 1929252938277203556570929)
                    ·
                      refine ⟨1446939703707902667428197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1929252938277203556570929 1446939703707902667428197)
                      ·
                        rfl

theorem cell23_2817905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 4, 2, 1, 3, 2].length) (baseStart_2817905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2817905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2817905 prefixEnd_2817905 := by exact prefixLift 2817905
  have htrace : WordTrace (prefixWord ++ tailWord_2817905) baseStart_2817905 baseEnd_2817905 := by
    simpa [prefixWord, tailWord_2817905, baseEnd_2817905] using wordTrace_append hprefix tailTrace_2817905
  have hstable : (prefixWord ++ tailWord_2817905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2817905).length < 2 ^ (prefixWord ++ tailWord_2817905).sum := by decide
  have hdescent : baseEnd_2817905 < baseStart_2817905 := by decide
  rcases family_descends (prefixWord ++ tailWord_2817905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2817991 : List Nat := [1, 1, 4, 1, 1, 2, 1, 2, 3, 3, 4]
def baseStart_2817991 : Nat := 118140960795 + 2817991 * 2 ^ 59
def prefixEnd_2817991 : Nat := 4983230072969 + 3 ^ 40 * 2817991 * 2
def baseEnd_2817991 : Nat := 1446983863044189330952801

theorem tailTrace_2817991 : CollatzResearch.WordTrace tailWord_2817991 prefixEnd_2817991 1446983863044189330952801 := by
  unfold tailWord_2817991
  simp only [CollatzResearch.WordTrace]
  refine ⟨102780575533907356391685827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68520383689271570927790551 102780575533907356391685827)
  ·
    refine ⟨154170863300861034587528741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102780575533907356391685827 154170863300861034587528741)
    ·
      refine ⟨28907036868911443985161639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 154170863300861034587528741 28907036868911443985161639)
      ·
        refine ⟨43360555303367165977742459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28907036868911443985161639 43360555303367165977742459)
        ·
          refine ⟨65040832955050748966613689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43360555303367165977742459 65040832955050748966613689)
          ·
            refine ⟨48780624716288061724960267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65040832955050748966613689 48780624716288061724960267)
            ·
              refine ⟨73170937074432092587440401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48780624716288061724960267 73170937074432092587440401)
              ·
                refine ⟨54878202805824069440580301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73170937074432092587440401 54878202805824069440580301)
                ·
                  refine ⟨20579326052184026040217613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54878202805824069440580301 20579326052184026040217613)
                  ·
                    refine ⟨7717247269569009765081605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20579326052184026040217613 7717247269569009765081605)
                    ·
                      refine ⟨1446983863044189330952801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7717247269569009765081605 1446983863044189330952801)
                      ·
                        rfl

theorem cell23_2817991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 2, 3, 3, 4].length) (baseStart_2817991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2817991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2817991 prefixEnd_2817991 := by exact prefixLift 2817991
  have htrace : WordTrace (prefixWord ++ tailWord_2817991) baseStart_2817991 baseEnd_2817991 := by
    simpa [prefixWord, tailWord_2817991, baseEnd_2817991] using wordTrace_append hprefix tailTrace_2817991
  have hstable : (prefixWord ++ tailWord_2817991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2817991).length < 2 ^ (prefixWord ++ tailWord_2817991).sum := by decide
  have hdescent : baseEnd_2817991 < baseStart_2817991 := by decide
  rcases family_descends (prefixWord ++ tailWord_2817991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2817992 : List Nat := [2, 1, 3, 1, 4, 3, 2, 2, 5]
def baseStart_2817992 : Nat := 118140960795 + 2817992 * 2 ^ 59
def prefixEnd_2817992 : Nat := 4983230072969 + 3 ^ 40 * 2817992 * 2
def baseEnd_2817992 : Nat := 160776041836093758560033

theorem tailTrace_2817992 : CollatzResearch.WordTrace tailWord_2817992 prefixEnd_2817992 160776041836093758560033 := by
  unfold tailWord_2817992
  simp only [CollatzResearch.WordTrace]
  refine ⟨51390306003451866781236115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68520408004602489041648153 51390306003451866781236115)
  ·
    refine ⟨77085459005177800171854173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51390306003451866781236115 77085459005177800171854173)
    ·
      refine ⟨28907047126941675064445315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77085459005177800171854173 28907047126941675064445315)
      ·
        refine ⟨43360570690412512596667973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28907047126941675064445315 43360570690412512596667973)
        ·
          refine ⟨8130107004452346111875245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43360570690412512596667973 8130107004452346111875245)
          ·
            refine ⟨3048790126669629791953217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8130107004452346111875245 3048790126669629791953217)
            ·
              refine ⟨2286592595002222343964913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3048790126669629791953217 2286592595002222343964913)
              ·
                refine ⟨1714944446251666757973685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2286592595002222343964913 1714944446251666757973685)
                ·
                  refine ⟨160776041836093758560033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1714944446251666757973685 160776041836093758560033)
                  ·
                    rfl

theorem cell23_2817992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 2, 2, 5].length) (baseStart_2817992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2817992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2817992 prefixEnd_2817992 := by exact prefixLift 2817992
  have htrace : WordTrace (prefixWord ++ tailWord_2817992) baseStart_2817992 baseEnd_2817992 := by
    simpa [prefixWord, tailWord_2817992, baseEnd_2817992] using wordTrace_append hprefix tailTrace_2817992
  have hstable : (prefixWord ++ tailWord_2817992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2817992).length < 2 ^ (prefixWord ++ tailWord_2817992).sum := by decide
  have hdescent : baseEnd_2817992 < baseStart_2817992 := by decide
  rcases family_descends (prefixWord ++ tailWord_2817992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2818031 : List Nat := [1, 1, 2, 1, 4, 2, 2, 2, 8]
def baseStart_2818031 : Nat := 118140960795 + 2818031 * 2 ^ 59
def prefixEnd_2818031 : Nat := 4983230072969 + 3 ^ 40 * 2818031 * 2
def baseEnd_2818031 : Nat := 160778266918929908272513

theorem tailTrace_2818031 : CollatzResearch.WordTrace tailWord_2818031 prefixEnd_2818031 160778266918929908272513 := by
  unfold tailWord_2818031
  simp only [CollatzResearch.WordTrace]
  refine ⟨102782034453762443223141947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68521356302508295482094631 102782034453762443223141947)
  ·
    refine ⟨154173051680643664834712921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102782034453762443223141947 154173051680643664834712921)
    ·
      refine ⟨115629788760482748626034691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154173051680643664834712921 115629788760482748626034691)
      ·
        refine ⟨173444683140724122939052037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115629788760482748626034691 173444683140724122939052037)
        ·
          refine ⟨32520878088885773051072257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 173444683140724122939052037 32520878088885773051072257)
          ·
            refine ⟨24390658566664329788304193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32520878088885773051072257 24390658566664329788304193)
            ·
              refine ⟨18292993924998247341228145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24390658566664329788304193 18292993924998247341228145)
              ·
                refine ⟨13719745443748685505921109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18292993924998247341228145 13719745443748685505921109)
                ·
                  refine ⟨160778266918929908272513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 13719745443748685505921109 160778266918929908272513)
                  ·
                    rfl

theorem cell23_2818031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 2, 8].length) (baseStart_2818031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2818031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2818031 prefixEnd_2818031 := by exact prefixLift 2818031
  have htrace : WordTrace (prefixWord ++ tailWord_2818031) baseStart_2818031 baseEnd_2818031 := by
    simpa [prefixWord, tailWord_2818031, baseEnd_2818031] using wordTrace_append hprefix tailTrace_2818031
  have hstable : (prefixWord ++ tailWord_2818031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2818031).length < 2 ^ (prefixWord ++ tailWord_2818031).sum := by decide
  have hdescent : baseEnd_2818031 < baseStart_2818031 := by decide
  rcases family_descends (prefixWord ++ tailWord_2818031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2818085 : List Nat := [1, 3, 1, 2, 2, 3, 2, 1, 1, 5, 2]
def baseStart_2818085 : Nat := 118140960795 + 2818085 * 2 ^ 59
def prefixEnd_2818085 : Nat := 4983230072969 + 3 ^ 40 * 2818085 * 2
def baseEnd_2818085 : Nat := 1447032130225711963177369

theorem tailTrace_2818085 : CollatzResearch.WordTrace tailWord_2818085 prefixEnd_2818085 1447032130225711963177369 := by
  unfold tailWord_2818085
  simp only [CollatzResearch.WordTrace]
  refine ⟨102784003995566810445607709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68522669330377873630405139 102784003995566810445607709)
  ·
    refine ⟨38544001498337553917102891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102784003995566810445607709 38544001498337553917102891)
    ·
      refine ⟨57816002247506330875654337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38544001498337553917102891 57816002247506330875654337)
      ·
        refine ⟨43362001685629748156740753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57816002247506330875654337 43362001685629748156740753)
        ·
          refine ⟨32521501264222311117555565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43362001685629748156740753 32521501264222311117555565)
          ·
            refine ⟨12195562974083366669083337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32521501264222311117555565 12195562974083366669083337)
            ·
              refine ⟨9146672230562525001812503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12195562974083366669083337 9146672230562525001812503)
              ·
                refine ⟨13720008345843787502718755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9146672230562525001812503 13720008345843787502718755)
                ·
                  refine ⟨20580012518765681254078133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13720008345843787502718755 20580012518765681254078133)
                  ·
                    refine ⟨1929376173634282617569825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 20580012518765681254078133 1929376173634282617569825)
                    ·
                      refine ⟨1447032130225711963177369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1929376173634282617569825 1447032130225711963177369)
                      ·
                        rfl

theorem cell23_2818085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 2, 1, 1, 5, 2].length) (baseStart_2818085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2818085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2818085 prefixEnd_2818085 := by exact prefixLift 2818085
  have htrace : WordTrace (prefixWord ++ tailWord_2818085) baseStart_2818085 baseEnd_2818085 := by
    simpa [prefixWord, tailWord_2818085, baseEnd_2818085] using wordTrace_append hprefix tailTrace_2818085
  have hstable : (prefixWord ++ tailWord_2818085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2818085).length < 2 ^ (prefixWord ++ tailWord_2818085).sum := by decide
  have hdescent : baseEnd_2818085 < baseStart_2818085 := by decide
  rcases family_descends (prefixWord ++ tailWord_2818085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2818092 : List Nat := [2, 2, 1, 1, 1, 2, 2, 7, 1, 1, 3]
def baseStart_2818092 : Nat := 118140960795 + 2818092 * 2 ^ 59
def prefixEnd_2818092 : Nat := 4983230072969 + 3 ^ 40 * 2818092 * 2
def baseEnd_2818092 : Nat := 1447035724590293435789837

theorem tailTrace_2818092 : CollatzResearch.WordTrace tailWord_2818092 prefixEnd_2818092 1447035724590293435789837 := by
  unfold tailWord_2818092
  simp only [CollatzResearch.WordTrace]
  refine ⟨51392129653270725320556265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68522839537694300427408353 51392129653270725320556265)
  ·
    refine ⟨38544097239953043990417199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51392129653270725320556265 38544097239953043990417199)
    ·
      refine ⟨57816145859929565985625799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38544097239953043990417199 57816145859929565985625799)
      ·
        refine ⟨86724218789894348978438699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57816145859929565985625799 86724218789894348978438699)
        ·
          refine ⟨130086328184841523467658049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86724218789894348978438699 130086328184841523467658049)
          ·
            refine ⟨97564746138631142600743537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 130086328184841523467658049 97564746138631142600743537)
            ·
              refine ⟨73173559603973356950557653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97564746138631142600743537 73173559603973356950557653)
              ·
                refine ⟨1715005303218125553528695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 73173559603973356950557653 1715005303218125553528695)
                ·
                  refine ⟨2572507954827188330293043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1715005303218125553528695 2572507954827188330293043)
                  ·
                    refine ⟨3858761932240782495439565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2572507954827188330293043 3858761932240782495439565)
                    ·
                      refine ⟨1447035724590293435789837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3858761932240782495439565 1447035724590293435789837)
                      ·
                        rfl

theorem cell23_2818092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 7, 1, 1, 3].length) (baseStart_2818092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2818092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2818092 prefixEnd_2818092 := by exact prefixLift 2818092
  have htrace : WordTrace (prefixWord ++ tailWord_2818092) baseStart_2818092 baseEnd_2818092 := by
    simpa [prefixWord, tailWord_2818092, baseEnd_2818092] using wordTrace_append hprefix tailTrace_2818092
  have hstable : (prefixWord ++ tailWord_2818092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2818092).length < 2 ^ (prefixWord ++ tailWord_2818092).sum := by decide
  have hdescent : baseEnd_2818092 < baseStart_2818092 := by decide
  rcases family_descends (prefixWord ++ tailWord_2818092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2818125 : List Nat := [1, 6, 1, 1, 1, 1, 2, 3, 1, 6]
def baseStart_2818125 : Nat := 118140960795 + 2818125 * 2 ^ 59
def prefixEnd_2818125 : Nat := 4983230072969 + 3 ^ 40 * 2818125 * 2
def baseEnd_2818125 : Nat := 482350889817297268892395

theorem tailTrace_2818125 : CollatzResearch.WordTrace tailWord_2818125 prefixEnd_2818125 482350889817297268892395 := by
  unfold tailWord_2818125
  simp only [CollatzResearch.WordTrace]
  refine ⟨102785462915421897277063829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68523641943614598184709219 102785462915421897277063829)
  ·
    refine ⟨4818068574160401434862367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 102785462915421897277063829 4818068574160401434862367)
    ·
      refine ⟨7227102861240602152293551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4818068574160401434862367 7227102861240602152293551)
      ·
        refine ⟨10840654291860903228440327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7227102861240602152293551 10840654291860903228440327)
        ·
          refine ⟨16260981437791354842660491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10840654291860903228440327 16260981437791354842660491)
          ·
            refine ⟨24391472156687032263990737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16260981437791354842660491 24391472156687032263990737)
            ·
              refine ⟨18293604117515274197993053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24391472156687032263990737 18293604117515274197993053)
              ·
                refine ⟨6860101544068227824247395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18293604117515274197993053 6860101544068227824247395)
                ·
                  refine ⟨10290152316102341736371093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6860101544068227824247395 10290152316102341736371093)
                  ·
                    refine ⟨482350889817297268892395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10290152316102341736371093 482350889817297268892395)
                    ·
                      rfl

theorem cell23_2818125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 3, 1, 6].length) (baseStart_2818125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2818125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2818125 prefixEnd_2818125 := by exact prefixLift 2818125
  have htrace : WordTrace (prefixWord ++ tailWord_2818125) baseStart_2818125 baseEnd_2818125 := by
    simpa [prefixWord, tailWord_2818125, baseEnd_2818125] using wordTrace_append hprefix tailTrace_2818125
  have hstable : (prefixWord ++ tailWord_2818125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2818125).length < 2 ^ (prefixWord ++ tailWord_2818125).sum := by decide
  have hdescent : baseEnd_2818125 < baseStart_2818125 := by decide
  rcases family_descends (prefixWord ++ tailWord_2818125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2818132 : List Nat := [2, 4, 1, 1, 1, 1, 1, 3, 5, 2, 2]
def baseStart_2818132 : Nat := 118140960795 + 2818132 * 2 ^ 59
def prefixEnd_2818132 : Nat := 4983230072969 + 3 ^ 40 * 2818132 * 2
def baseEnd_2818132 : Nat := 1447056263816473279289653

theorem tailTrace_2818132 : CollatzResearch.WordTrace tailWord_2818132 prefixEnd_2818132 1447056263816473279289653 := by
  unfold tailWord_2818132
  simp only [CollatzResearch.WordTrace]
  refine ⟨51392859113198268736284325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68523812150931024981712433 51392859113198268736284325)
  ·
    refine ⟨9636161083724675388053311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51392859113198268736284325 9636161083724675388053311)
    ·
      refine ⟨14454241625587013082079967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9636161083724675388053311 14454241625587013082079967)
      ·
        refine ⟨21681362438380519623119951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14454241625587013082079967 21681362438380519623119951)
        ·
          refine ⟨32522043657570779434679927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21681362438380519623119951 32522043657570779434679927)
          ·
            refine ⟨48783065486356169152019891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32522043657570779434679927 48783065486356169152019891)
            ·
              refine ⟨73174598229534253728029837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48783065486356169152019891 73174598229534253728029837)
              ·
                refine ⟨27440474336075345148011189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 73174598229534253728029837 27440474336075345148011189)
                ·
                  refine ⟨2572544469007063607626049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27440474336075345148011189 2572544469007063607626049)
                  ·
                    refine ⟨1929408351755297705719537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2572544469007063607626049 1929408351755297705719537)
                    ·
                      refine ⟨1447056263816473279289653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1929408351755297705719537 1447056263816473279289653)
                      ·
                        rfl

theorem cell23_2818132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 3, 5, 2, 2].length) (baseStart_2818132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2818132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2818132 prefixEnd_2818132 := by exact prefixLift 2818132
  have htrace : WordTrace (prefixWord ++ tailWord_2818132) baseStart_2818132 baseEnd_2818132 := by
    simpa [prefixWord, tailWord_2818132, baseEnd_2818132] using wordTrace_append hprefix tailTrace_2818132
  have hstable : (prefixWord ++ tailWord_2818132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2818132).length < 2 ^ (prefixWord ++ tailWord_2818132).sum := by decide
  have hdescent : baseEnd_2818132 < baseStart_2818132 := by decide
  rcases family_descends (prefixWord ++ tailWord_2818132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2818192 : List Nat := [2, 1, 1, 1, 1, 1, 6, 4, 1, 3, 2]
def baseStart_2818192 : Nat := 118140960795 + 2818192 * 2 ^ 59
def prefixEnd_2818192 : Nat := 4983230072969 + 3 ^ 40 * 2818192 * 2
def baseEnd_2818192 : Nat := 1447087072655743044539377

theorem tailTrace_2818192 : CollatzResearch.WordTrace tailWord_2818192 prefixEnd_2818192 1447087072655743044539377 := by
  unfold tailWord_2818192
  simp only [CollatzResearch.WordTrace]
  refine ⟨51393953303089583859876415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68525271070786111813168553 51393953303089583859876415)
  ·
    refine ⟨77090929954634375789814623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51393953303089583859876415 77090929954634375789814623)
    ·
      refine ⟨115636394931951563684721935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77090929954634375789814623 115636394931951563684721935)
      ·
        refine ⟨173454592397927345527082903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115636394931951563684721935 173454592397927345527082903)
        ·
          refine ⟨260181888596891018290624355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173454592397927345527082903 260181888596891018290624355)
          ·
            refine ⟨390272832895336527435936533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 260181888596891018290624355 390272832895336527435936533)
            ·
              refine ⟨18294039041968899723559525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 390272832895336527435936533 18294039041968899723559525)
              ·
                refine ⟨3430132320369168698167411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18294039041968899723559525 3430132320369168698167411)
                ·
                  refine ⟨5145198480553753047251117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3430132320369168698167411 5145198480553753047251117)
                  ·
                    refine ⟨1929449430207657392719169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5145198480553753047251117 1929449430207657392719169)
                    ·
                      refine ⟨1447087072655743044539377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1929449430207657392719169 1447087072655743044539377)
                      ·
                        rfl

theorem cell23_2818192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 4, 1, 3, 2].length) (baseStart_2818192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2818192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2818192 prefixEnd_2818192 := by exact prefixLift 2818192
  have htrace : WordTrace (prefixWord ++ tailWord_2818192) baseStart_2818192 baseEnd_2818192 := by
    simpa [prefixWord, tailWord_2818192, baseEnd_2818192] using wordTrace_append hprefix tailTrace_2818192
  have hstable : (prefixWord ++ tailWord_2818192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2818192).length < 2 ^ (prefixWord ++ tailWord_2818192).sum := by decide
  have hdescent : baseEnd_2818192 < baseStart_2818192 := by decide
  rcases family_descends (prefixWord ++ tailWord_2818192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2818209 : List Nat := [1, 2, 3, 3, 1, 3, 1, 3, 1, 3, 2]
def baseStart_2818209 : Nat := 118140960795 + 2818209 * 2 ^ 59
def prefixEnd_2818209 : Nat := 4983230072969 + 3 ^ 40 * 2818209 * 2
def baseEnd_2818209 : Nat := 1447095801826869478026799

theorem tailTrace_2818209 : CollatzResearch.WordTrace tailWord_2818209 prefixEnd_2818209 1447095801826869478026799 := by
  unfold tailWord_2818209
  simp only [CollatzResearch.WordTrace]
  refine ⟨102788526647117579623121681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68525684431411719748747787 102788526647117579623121681)
  ·
    refine ⟨77091394985338184717341261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102788526647117579623121681 77091394985338184717341261)
    ·
      refine ⟨28909273119501819269002973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77091394985338184717341261 28909273119501819269002973)
      ·
        refine ⟨10840977419813182225876115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28909273119501819269002973 10840977419813182225876115)
        ·
          refine ⟨16261466129719773338814173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10840977419813182225876115 16261466129719773338814173)
          ·
            refine ⟨6098049798644915002055315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16261466129719773338814173 6098049798644915002055315)
            ·
              refine ⟨9147074697967372503082973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6098049798644915002055315 9147074697967372503082973)
              ·
                refine ⟨3430153011737764688656115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9147074697967372503082973 3430153011737764688656115)
                ·
                  refine ⟨5145229517606647032984173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3430153011737764688656115 5145229517606647032984173)
                  ·
                    refine ⟨1929461069102492637369065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5145229517606647032984173 1929461069102492637369065)
                    ·
                      refine ⟨1447095801826869478026799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1929461069102492637369065 1447095801826869478026799)
                      ·
                        rfl

theorem cell23_2818209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 1, 3, 1, 3, 2].length) (baseStart_2818209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2818209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2818209 prefixEnd_2818209 := by exact prefixLift 2818209
  have htrace : WordTrace (prefixWord ++ tailWord_2818209) baseStart_2818209 baseEnd_2818209 := by
    simpa [prefixWord, tailWord_2818209, baseEnd_2818209] using wordTrace_append hprefix tailTrace_2818209
  have hstable : (prefixWord ++ tailWord_2818209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2818209).length < 2 ^ (prefixWord ++ tailWord_2818209).sum := by decide
  have hdescent : baseEnd_2818209 < baseStart_2818209 := by decide
  rcases family_descends (prefixWord ++ tailWord_2818209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2818282 : List Nat := [3, 1, 3, 1, 1, 2, 2, 1, 2, 5, 2]
def baseStart_2818282 : Nat := 118140960795 + 2818282 * 2 ^ 59
def prefixEnd_2818282 : Nat := 4983230072969 + 3 ^ 40 * 2818282 * 2
def baseEnd_2818282 : Nat := 1447133285914647692413963

theorem tailTrace_2818282 : CollatzResearch.WordTrace tailWord_2818282 prefixEnd_2818282 1447133285914647692413963 := by
  unfold tailWord_2818282
  simp only [CollatzResearch.WordTrace]
  refine ⟨25697797293963278272632275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68527459450568742060352733 25697797293963278272632275)
  ·
    refine ⟨38546695940944917408948413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25697797293963278272632275 38546695940944917408948413)
    ·
      refine ⟨14455010977854344028355655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38546695940944917408948413 14455010977854344028355655)
      ·
        refine ⟨21682516466781516042533483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14455010977854344028355655 21682516466781516042533483)
        ·
          refine ⟨32523774700172274063800225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21682516466781516042533483 32523774700172274063800225)
          ·
            refine ⟨24392831025129205547850169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32523774700172274063800225 24392831025129205547850169)
            ·
              refine ⟨18294623268846904160887627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24392831025129205547850169 18294623268846904160887627)
              ·
                refine ⟨27441934903270356241331441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18294623268846904160887627 27441934903270356241331441)
                ·
                  refine ⟨20581451177452767180998581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27441934903270356241331441 20581451177452767180998581)
                  ·
                    refine ⟨1929511047886196923218617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 20581451177452767180998581 1929511047886196923218617)
                    ·
                      refine ⟨1447133285914647692413963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1929511047886196923218617 1447133285914647692413963)
                      ·
                        rfl

theorem cell23_2818282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 1, 2, 5, 2].length) (baseStart_2818282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2818282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2818282 prefixEnd_2818282 := by exact prefixLift 2818282
  have htrace : WordTrace (prefixWord ++ tailWord_2818282) baseStart_2818282 baseEnd_2818282 := by
    simpa [prefixWord, tailWord_2818282, baseEnd_2818282] using wordTrace_append hprefix tailTrace_2818282
  have hstable : (prefixWord ++ tailWord_2818282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2818282).length < 2 ^ (prefixWord ++ tailWord_2818282).sum := by decide
  have hdescent : baseEnd_2818282 < baseStart_2818282 := by decide
  rcases family_descends (prefixWord ++ tailWord_2818282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2818312 : List Nat := [2, 1, 3, 2, 3, 1, 1, 3, 2, 1, 4]
def baseStart_2818312 : Nat := 118140960795 + 2818312 * 2 ^ 59
def prefixEnd_2818312 : Nat := 4983230072969 + 3 ^ 40 * 2818312 * 2
def baseEnd_2818312 : Nat := 1447148690334282575038825

theorem tailTrace_2818312 : CollatzResearch.WordTrace tailWord_2818312 prefixEnd_2818312 1447148690334282575038825 := by
  unfold tailWord_2818312
  simp only [CollatzResearch.WordTrace]
  refine ⟨51396141682872214107060595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68528188910496285476080793 51396141682872214107060595)
  ·
    refine ⟨77094212524308321160590893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51396141682872214107060595 77094212524308321160590893)
    ·
      refine ⟨28910329696615620435221585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77094212524308321160590893 28910329696615620435221585)
      ·
        refine ⟨21682747272461715326416189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28910329696615620435221585 21682747272461715326416189)
        ·
          refine ⟨8131030227173143247406071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21682747272461715326416189 8131030227173143247406071)
          ·
            refine ⟨12196545340759714871109107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8131030227173143247406071 12196545340759714871109107)
            ·
              refine ⟨18294818011139572306663661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12196545340759714871109107 18294818011139572306663661)
              ·
                refine ⟨6860556754177339614998873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18294818011139572306663661 6860556754177339614998873)
                ·
                  refine ⟨5145417565633004711249155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6860556754177339614998873 5145417565633004711249155)
                  ·
                    refine ⟨7718126348449507066873733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5145417565633004711249155 7718126348449507066873733)
                    ·
                      refine ⟨1447148690334282575038825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7718126348449507066873733 1447148690334282575038825)
                      ·
                        rfl

theorem cell23_2818312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 3, 2, 1, 4].length) (baseStart_2818312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2818312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2818312 prefixEnd_2818312 := by exact prefixLift 2818312
  have htrace : WordTrace (prefixWord ++ tailWord_2818312) baseStart_2818312 baseEnd_2818312 := by
    simpa [prefixWord, tailWord_2818312, baseEnd_2818312] using wordTrace_append hprefix tailTrace_2818312
  have hstable : (prefixWord ++ tailWord_2818312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2818312).length < 2 ^ (prefixWord ++ tailWord_2818312).sum := by decide
  have hdescent : baseEnd_2818312 < baseStart_2818312 := by decide
  rcases family_descends (prefixWord ++ tailWord_2818312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2818339 : List Nat := [1, 1, 1, 4, 2, 2, 3, 4, 1, 4]
def baseStart_2818339 : Nat := 118140960795 + 2818339 * 2 ^ 59
def prefixEnd_2818339 : Nat := 4983230072969 + 3 ^ 40 * 2818339 * 2
def baseEnd_2818339 : Nat := 482387518103984656467067

theorem tailTrace_2818339 : CollatzResearch.WordTrace tailWord_2818339 prefixEnd_2818339 482387518103984656467067 := by
  unfold tailWord_2818339
  simp only [CollatzResearch.WordTrace]
  refine ⟨102793268136646611825354071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68528845424431074550236047 102793268136646611825354071)
  ·
    refine ⟨154189902204969917738031107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102793268136646611825354071 154189902204969917738031107)
    ·
      refine ⟨231284853307454876607046661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154189902204969917738031107 231284853307454876607046661)
      ·
        refine ⟨43365909995147789363821249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 231284853307454876607046661 43365909995147789363821249)
        ·
          refine ⟨32524432496360842022865937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43365909995147789363821249 32524432496360842022865937)
          ·
            refine ⟨24393324372270631517149453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32524432496360842022865937 24393324372270631517149453)
            ·
              refine ⟨9147496639601486818931045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24393324372270631517149453 9147496639601486818931045)
              ·
                refine ⟨1715155619925278778549571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9147496639601486818931045 1715155619925278778549571)
                ·
                  refine ⟨2572733429887918167824357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1715155619925278778549571 2572733429887918167824357)
                  ·
                    refine ⟨482387518103984656467067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2572733429887918167824357 482387518103984656467067)
                    ·
                      rfl

theorem cell23_2818339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 3, 4, 1, 4].length) (baseStart_2818339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2818339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2818339 prefixEnd_2818339 := by exact prefixLift 2818339
  have htrace : WordTrace (prefixWord ++ tailWord_2818339) baseStart_2818339 baseEnd_2818339 := by
    simpa [prefixWord, tailWord_2818339, baseEnd_2818339] using wordTrace_append hprefix tailTrace_2818339
  have hstable : (prefixWord ++ tailWord_2818339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2818339).length < 2 ^ (prefixWord ++ tailWord_2818339).sum := by decide
  have hdescent : baseEnd_2818339 < baseStart_2818339 := by decide
  rcases family_descends (prefixWord ++ tailWord_2818339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2818346 : List Nat := [3, 1, 4, 2, 2, 1, 1, 1, 2, 4, 2]
def baseStart_2818346 : Nat := 118140960795 + 2818346 * 2 ^ 59
def prefixEnd_2818346 : Nat := 4983230072969 + 3 ^ 40 * 2818346 * 2
def baseEnd_2818346 : Nat := 1447166148676535442013669

theorem tailTrace_2818346 : CollatzResearch.WordTrace tailWord_2818346 prefixEnd_2818346 1447166148676535442013669 := by
  unfold tailWord_2818346
  simp only [CollatzResearch.WordTrace]
  refine ⟨25698380861905313005214723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68529015631747501347239261 25698380861905313005214723)
  ·
    refine ⟨38547571292857969507822085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25698380861905313005214723 38547571292857969507822085)
    ·
      refine ⟨7227669617410869282716641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38547571292857969507822085 7227669617410869282716641)
      ·
        refine ⟨5420752213058151962037481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7227669617410869282716641 5420752213058151962037481)
        ·
          refine ⟨4065564159793613971528111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5420752213058151962037481 4065564159793613971528111)
          ·
            refine ⟨6098346239690420957292167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4065564159793613971528111 6098346239690420957292167)
            ·
              refine ⟨9147519359535631435938251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6098346239690420957292167 9147519359535631435938251)
              ·
                refine ⟨13721279039303447153907377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9147519359535631435938251 13721279039303447153907377)
                ·
                  refine ⟨10290959279477585365430533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13721279039303447153907377 10290959279477585365430533)
                  ·
                    refine ⟨1929554864902047256018225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10290959279477585365430533 1929554864902047256018225)
                    ·
                      refine ⟨1447166148676535442013669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1929554864902047256018225 1447166148676535442013669)
                      ·
                        rfl

theorem cell23_2818346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 1, 1, 2, 4, 2].length) (baseStart_2818346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2818346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2818346 prefixEnd_2818346 := by exact prefixLift 2818346
  have htrace : WordTrace (prefixWord ++ tailWord_2818346) baseStart_2818346 baseEnd_2818346 := by
    simpa [prefixWord, tailWord_2818346, baseEnd_2818346] using wordTrace_append hprefix tailTrace_2818346
  have hstable : (prefixWord ++ tailWord_2818346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2818346).length < 2 ^ (prefixWord ++ tailWord_2818346).sum := by decide
  have hdescent : baseEnd_2818346 < baseStart_2818346 := by decide
  rcases family_descends (prefixWord ++ tailWord_2818346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2818366 : List Nat := [4, 2, 1, 2, 1, 4, 1, 1, 2, 2, 3]
def baseStart_2818366 : Nat := 118140960795 + 2818366 * 2 ^ 59
def prefixEnd_2818366 : Nat := 4983230072969 + 3 ^ 40 * 2818366 * 2
def baseEnd_2818366 : Nat := 1447176418289625363763577

theorem tailTrace_2818366 : CollatzResearch.WordTrace tailWord_2818366 prefixEnd_2818366 1447176418289625363763577 := by
  unfold tailWord_2818366
  simp only [CollatzResearch.WordTrace]
  refine ⟨12849281613443599429573369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68529501938365863624391301 12849281613443599429573369)
  ·
    refine ⟨9636961210082699572180027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12849281613443599429573369 9636961210082699572180027)
    ·
      refine ⟨14455441815124049358270041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9636961210082699572180027 14455441815124049358270041)
      ·
        refine ⟨10841581361343037018702531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14455441815124049358270041 10841581361343037018702531)
        ·
          refine ⟨16262372042014555528053797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10841581361343037018702531 16262372042014555528053797)
          ·
            refine ⟨3049194757877729161510087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16262372042014555528053797 3049194757877729161510087)
            ·
              refine ⟨4573792136816593742265131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3049194757877729161510087 4573792136816593742265131)
              ·
                refine ⟨6860688205224890613397697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4573792136816593742265131 6860688205224890613397697)
                ·
                  refine ⟨5145516153918667960048273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6860688205224890613397697 5145516153918667960048273)
                  ·
                    refine ⟨3859137115439000970036205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5145516153918667960048273 3859137115439000970036205)
                    ·
                      refine ⟨1447176418289625363763577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3859137115439000970036205 1447176418289625363763577)
                      ·
                        rfl

theorem cell23_2818366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 1, 1, 2, 2, 3].length) (baseStart_2818366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2818366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2818366 prefixEnd_2818366 := by exact prefixLift 2818366
  have htrace : WordTrace (prefixWord ++ tailWord_2818366) baseStart_2818366 baseEnd_2818366 := by
    simpa [prefixWord, tailWord_2818366, baseEnd_2818366] using wordTrace_append hprefix tailTrace_2818366
  have hstable : (prefixWord ++ tailWord_2818366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2818366).length < 2 ^ (prefixWord ++ tailWord_2818366).sum := by decide
  have hdescent : baseEnd_2818366 < baseStart_2818366 := by decide
  rcases family_descends (prefixWord ++ tailWord_2818366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2818439 : List Nat := [1, 1, 4, 2, 2, 1, 1, 5, 1, 2, 3]
def baseStart_2818439 : Nat := 118140960795 + 2818439 * 2 ^ 59
def prefixEnd_2818439 : Nat := 4983230072969 + 3 ^ 40 * 2818439 * 2
def baseEnd_2818439 : Nat := 1447213902377403578150741

theorem tailTrace_2818439 : CollatzResearch.WordTrace tailWord_2818439 prefixEnd_2818439 1447213902377403578150741 := by
  unfold tailWord_2818439
  simp only [CollatzResearch.WordTrace]
  refine ⟨102796915436284328903994371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68531276957522885935996247 102796915436284328903994371)
  ·
    refine ⟨154195373154426493355991557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102796915436284328903994371 154195373154426493355991557)
    ·
      refine ⟨28911632466454967504248417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 154195373154426493355991557 28911632466454967504248417)
      ·
        refine ⟨21683724349841225628186313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28911632466454967504248417 21683724349841225628186313)
        ·
          refine ⟨16262793262380919221139735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21683724349841225628186313 16262793262380919221139735)
          ·
            refine ⟨24394189893571378831709603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16262793262380919221139735 24394189893571378831709603)
            ·
              refine ⟨36591284840357068247564405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24394189893571378831709603 36591284840357068247564405)
              ·
                refine ⟨3430432953783475148209163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36591284840357068247564405 3430432953783475148209163)
                ·
                  refine ⟨5145649430675212722313745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3430432953783475148209163 5145649430675212722313745)
                  ·
                    refine ⟨3859237073006409541735309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5145649430675212722313745 3859237073006409541735309)
                    ·
                      refine ⟨1447213902377403578150741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3859237073006409541735309 1447213902377403578150741)
                      ·
                        rfl

theorem cell23_2818439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 5, 1, 2, 3].length) (baseStart_2818439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2818439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2818439 prefixEnd_2818439 := by exact prefixLift 2818439
  have htrace : WordTrace (prefixWord ++ tailWord_2818439) baseStart_2818439 baseEnd_2818439 := by
    simpa [prefixWord, tailWord_2818439, baseEnd_2818439] using wordTrace_append hprefix tailTrace_2818439
  have hstable : (prefixWord ++ tailWord_2818439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2818439).length < 2 ^ (prefixWord ++ tailWord_2818439).sum := by decide
  have hdescent : baseEnd_2818439 < baseStart_2818439 := by decide
  rcases family_descends (prefixWord ++ tailWord_2818439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2818569 : List Nat := [1, 2, 1, 1, 3, 1, 2, 3, 2, 5, 2]
def baseStart_2818569 : Nat := 118140960795 + 2818569 * 2 ^ 59
def prefixEnd_2818569 : Nat := 4983230072969 + 3 ^ 40 * 2818569 * 2
def baseEnd_2818569 : Nat := 1447280654862488069525143

theorem tailTrace_2818569 : CollatzResearch.WordTrace tailWord_2818569 prefixEnd_2818569 1447280654862488069525143 := by
  unfold tailWord_2818569
  simp only [CollatzResearch.WordTrace]
  refine ⟨102801656925813361106226761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68534437950542240737484507 102801656925813361106226761)
  ·
    refine ⟨77101242694360020829670071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102801656925813361106226761 77101242694360020829670071)
    ·
      refine ⟨115651864041540031244505107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77101242694360020829670071 115651864041540031244505107)
      ·
        refine ⟨173477796062310046866757661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115651864041540031244505107 173477796062310046866757661)
        ·
          refine ⟨65054173523366267575034123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 173477796062310046866757661 65054173523366267575034123)
          ·
            refine ⟨97581260285049401362551185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65054173523366267575034123 97581260285049401362551185)
            ·
              refine ⟨73185945213787051021913389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97581260285049401362551185 73185945213787051021913389)
              ·
                refine ⟨27444729455170144133217521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 73185945213787051021913389 27444729455170144133217521)
                ·
                  refine ⟨20583547091377608099913141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27444729455170144133217521 20583547091377608099913141)
                  ·
                    refine ⟨1929707539816650759366857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 20583547091377608099913141 1929707539816650759366857)
                    ·
                      refine ⟨1447280654862488069525143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1929707539816650759366857 1447280654862488069525143)
                      ·
                        rfl

theorem cell23_2818569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 3, 2, 5, 2].length) (baseStart_2818569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2818569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2818569 prefixEnd_2818569 := by exact prefixLift 2818569
  have htrace : WordTrace (prefixWord ++ tailWord_2818569) baseStart_2818569 baseEnd_2818569 := by
    simpa [prefixWord, tailWord_2818569, baseEnd_2818569] using wordTrace_append hprefix tailTrace_2818569
  have hstable : (prefixWord ++ tailWord_2818569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2818569).length < 2 ^ (prefixWord ++ tailWord_2818569).sum := by decide
  have hdescent : baseEnd_2818569 < baseStart_2818569 := by decide
  rcases family_descends (prefixWord ++ tailWord_2818569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2818573 : List Nat := [1, 7, 1, 1, 1, 1, 2, 1, 2, 2, 4]
def baseStart_2818573 : Nat := 118140960795 + 2818573 * 2 ^ 59
def prefixEnd_2818573 : Nat := 4983230072969 + 3 ^ 40 * 2818573 * 2
def baseEnd_2818573 : Nat := 1447282708785106053875125

theorem tailTrace_2818573 : CollatzResearch.WordTrace tailWord_2818573 prefixEnd_2818573 1447282708785106053875125 := by
  unfold tailWord_2818573
  simp only [CollatzResearch.WordTrace]
  refine ⟨102801802817798869789372373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68534535211865913192914915 102801802817798869789372373)
  ·
    refine ⟨2409417253542161010688415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 102801802817798869789372373 2409417253542161010688415)
    ·
      refine ⟨3614125880313241516032623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2409417253542161010688415 3614125880313241516032623)
      ·
        refine ⟨5421188820469862274048935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3614125880313241516032623 5421188820469862274048935)
        ·
          refine ⟨8131783230704793411073403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5421188820469862274048935 8131783230704793411073403)
          ·
            refine ⟨12197674846057190116610105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8131783230704793411073403 12197674846057190116610105)
            ·
              refine ⟨9148256134542892587457579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12197674846057190116610105 9148256134542892587457579)
              ·
                refine ⟨13722384201814338881186369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9148256134542892587457579 13722384201814338881186369)
                ·
                  refine ⟨10291788151360754160889777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13722384201814338881186369 10291788151360754160889777)
                  ·
                    refine ⟨7718841113520565620667333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10291788151360754160889777 7718841113520565620667333)
                    ·
                      refine ⟨1447282708785106053875125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7718841113520565620667333 1447282708785106053875125)
                      ·
                        rfl

theorem cell23_2818573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 2, 1, 2, 2, 4].length) (baseStart_2818573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2818573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2818573 prefixEnd_2818573 := by exact prefixLift 2818573
  have htrace : WordTrace (prefixWord ++ tailWord_2818573) baseStart_2818573 baseEnd_2818573 := by
    simpa [prefixWord, tailWord_2818573, baseEnd_2818573] using wordTrace_append hprefix tailTrace_2818573
  have hstable : (prefixWord ++ tailWord_2818573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2818573).length < 2 ^ (prefixWord ++ tailWord_2818573).sum := by decide
  have hdescent : baseEnd_2818573 < baseStart_2818573 := by decide
  rcases family_descends (prefixWord ++ tailWord_2818573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2818609 : List Nat := [1, 2, 2, 3, 1, 1, 2, 2, 5, 4]
def baseStart_2818609 : Nat := 118140960795 + 2818609 * 2 ^ 59
def prefixEnd_2818609 : Nat := 4983230072969 + 3 ^ 40 * 2818609 * 2
def baseEnd_2818609 : Nat := 482433731362889304341653

theorem tailTrace_2818609 : CollatzResearch.WordTrace tailWord_2818609 prefixEnd_2818609 482433731362889304341653 := by
  unfold tailWord_2818609
  simp only [CollatzResearch.WordTrace]
  refine ⟨102803115845668447937682881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68535410563778965291788587 102803115845668447937682881)
  ·
    refine ⟨77102336884251335953262161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102803115845668447937682881 77102336884251335953262161)
    ·
      refine ⟨57826752663188501964946621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77102336884251335953262161 57826752663188501964946621)
      ·
        refine ⟨21685032248695688236854983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57826752663188501964946621 21685032248695688236854983)
        ·
          refine ⟨32527548373043532355282475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21685032248695688236854983 32527548373043532355282475)
          ·
            refine ⟨48791322559565298532923713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32527548373043532355282475 48791322559565298532923713)
            ·
              refine ⟨36593491919673973899692785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48791322559565298532923713 36593491919673973899692785)
              ·
                refine ⟨27445118939755480424769589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36593491919673973899692785 27445118939755480424769589)
                ·
                  refine ⟨2572979900602076289822149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27445118939755480424769589 2572979900602076289822149)
                  ·
                    refine ⟨482433731362889304341653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2572979900602076289822149 482433731362889304341653)
                    ·
                      rfl

theorem cell23_2818609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 2, 5, 4].length) (baseStart_2818609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2818609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2818609 prefixEnd_2818609 := by exact prefixLift 2818609
  have htrace : WordTrace (prefixWord ++ tailWord_2818609) baseStart_2818609 baseEnd_2818609 := by
    simpa [prefixWord, tailWord_2818609, baseEnd_2818609] using wordTrace_append hprefix tailTrace_2818609
  have hstable : (prefixWord ++ tailWord_2818609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2818609).length < 2 ^ (prefixWord ++ tailWord_2818609).sum := by decide
  have hdescent : baseEnd_2818609 < baseStart_2818609 := by decide
  rcases family_descends (prefixWord ++ tailWord_2818609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2818628 : List Nat := [2, 3, 5, 1, 2, 1, 2, 1, 2, 2, 2]
def baseStart_2818628 : Nat := 118140960795 + 2818628 * 2 ^ 59
def prefixEnd_2818628 : Nat := 4983230072969 + 3 ^ 40 * 2818628 * 2
def baseEnd_2818628 : Nat := 1447310950221103338687373

theorem tailTrace_2818628 : CollatzResearch.WordTrace tailWord_2818628 prefixEnd_2818628 1447310950221103338687373 := by
  unfold tailWord_2818628
  simp only [CollatzResearch.WordTrace]
  refine ⟨51401904416299807091312269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68535872555066409455083025 51401904416299807091312269)
  ·
    refine ⟨19275714156112427659242101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51401904416299807091312269 19275714156112427659242101)
    ·
      refine ⟨1807098202135540093053947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 19275714156112427659242101 1807098202135540093053947)
      ·
        refine ⟨2710647303203310139580921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1807098202135540093053947 2710647303203310139580921)
        ·
          refine ⟨2032985477402482604685691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2710647303203310139580921 2032985477402482604685691)
          ·
            refine ⟨3049478216103723907028537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2032985477402482604685691 3049478216103723907028537)
            ·
              refine ⟨2287108662077792930271403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3049478216103723907028537 2287108662077792930271403)
              ·
                refine ⟨3430662993116689395407105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2287108662077792930271403 3430662993116689395407105)
                ·
                  refine ⟨2572997244837517046555329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3430662993116689395407105 2572997244837517046555329)
                  ·
                    refine ⟨1929747933628137784916497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2572997244837517046555329 1929747933628137784916497)
                    ·
                      refine ⟨1447310950221103338687373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1929747933628137784916497 1447310950221103338687373)
                      ·
                        rfl

theorem cell23_2818628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 2, 1, 2, 2, 2].length) (baseStart_2818628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2818628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2818628 prefixEnd_2818628 := by exact prefixLift 2818628
  have htrace : WordTrace (prefixWord ++ tailWord_2818628) baseStart_2818628 baseEnd_2818628 := by
    simpa [prefixWord, tailWord_2818628, baseEnd_2818628] using wordTrace_append hprefix tailTrace_2818628
  have hstable : (prefixWord ++ tailWord_2818628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2818628).length < 2 ^ (prefixWord ++ tailWord_2818628).sum := by decide
  have hdescent : baseEnd_2818628 < baseStart_2818628 := by decide
  rcases family_descends (prefixWord ++ tailWord_2818628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2818716 : List Nat := [2, 2, 3, 2, 2, 1, 2, 2, 1, 6]
def baseStart_2818716 : Nat := 118140960795 + 2818716 * 2 ^ 59
def prefixEnd_2818716 : Nat := 4983230072969 + 3 ^ 40 * 2818716 * 2
def baseEnd_2818716 : Nat := 482452045506232998128989

theorem tailTrace_2818716 : CollatzResearch.WordTrace tailWord_2818716 prefixEnd_2818716 482452045506232998128989 := by
  unfold tailWord_2818716
  simp only [CollatzResearch.WordTrace]
  refine ⟨51403509228140402605914001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68538012304187203474552001 51403509228140402605914001)
  ·
    refine ⟨38552631921105301954435501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51403509228140402605914001 38552631921105301954435501)
    ·
      refine ⟨14457236970414488232913313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38552631921105301954435501 14457236970414488232913313)
      ·
        refine ⟨10842927727810866174684985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14457236970414488232913313 10842927727810866174684985)
        ·
          refine ⟨8132195795858149631013739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10842927727810866174684985 8132195795858149631013739)
          ·
            refine ⟨12198293693787224446520609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8132195795858149631013739 12198293693787224446520609)
            ·
              refine ⟨9148720270340418334890457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12198293693787224446520609 9148720270340418334890457)
              ·
                refine ⟨6861540202755313751167843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9148720270340418334890457 6861540202755313751167843)
                ·
                  refine ⟨10292310304132970626751765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6861540202755313751167843 10292310304132970626751765)
                  ·
                    refine ⟨482452045506232998128989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10292310304132970626751765 482452045506232998128989)
                    ·
                      rfl

theorem cell23_2818716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 2, 2, 1, 6].length) (baseStart_2818716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2818716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2818716 prefixEnd_2818716 := by exact prefixLift 2818716
  have htrace : WordTrace (prefixWord ++ tailWord_2818716) baseStart_2818716 baseEnd_2818716 := by
    simpa [prefixWord, tailWord_2818716, baseEnd_2818716] using wordTrace_append hprefix tailTrace_2818716
  have hstable : (prefixWord ++ tailWord_2818716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2818716).length < 2 ^ (prefixWord ++ tailWord_2818716).sum := by decide
  have hdescent : baseEnd_2818716 < baseStart_2818716 := by decide
  rcases family_descends (prefixWord ++ tailWord_2818716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2818720 : List Nat := [2, 1, 1, 4, 4, 2, 2, 1, 1, 5]
def baseStart_2818720 : Nat := 118140960795 + 2818720 * 2 ^ 59
def prefixEnd_2818720 : Nat := 4983230072969 + 3 ^ 40 * 2818720 * 2
def baseEnd_2818720 : Nat := 482452730147105659578983

theorem tailTrace_2818720 : CollatzResearch.WordTrace tailWord_2818720 prefixEnd_2818720 482452730147105659578983 := by
  unfold tailWord_2818720
  simp only [CollatzResearch.WordTrace]
  refine ⟨51403582174133156947486807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68538109565510875929982409 51403582174133156947486807)
  ·
    refine ⟨77105373261199735421230211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51403582174133156947486807 77105373261199735421230211)
    ·
      refine ⟨115658059891799603131845317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77105373261199735421230211 115658059891799603131845317)
      ·
        refine ⟨21685886229712425587220997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 115658059891799603131845317 21685886229712425587220997)
        ·
          refine ⟨4066103668071079797603937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21685886229712425587220997 4066103668071079797603937)
          ·
            refine ⟨3049577751053309848202953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4066103668071079797603937 3049577751053309848202953)
            ·
              refine ⟨2287183313289982386152215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3049577751053309848202953 2287183313289982386152215)
              ·
                refine ⟨3430774969934973579228323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2287183313289982386152215 3430774969934973579228323)
                ·
                  refine ⟨5146162454902460368842485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3430774969934973579228323 5146162454902460368842485)
                  ·
                    refine ⟨482452730147105659578983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5146162454902460368842485 482452730147105659578983)
                    ·
                      rfl

theorem cell23_2818720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 2, 1, 1, 5].length) (baseStart_2818720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2818720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2818720 prefixEnd_2818720 := by exact prefixLift 2818720
  have htrace : WordTrace (prefixWord ++ tailWord_2818720) baseStart_2818720 baseEnd_2818720 := by
    simpa [prefixWord, tailWord_2818720, baseEnd_2818720] using wordTrace_append hprefix tailTrace_2818720
  have hstable : (prefixWord ++ tailWord_2818720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2818720).length < 2 ^ (prefixWord ++ tailWord_2818720).sum := by decide
  have hdescent : baseEnd_2818720 < baseStart_2818720 := by decide
  rcases family_descends (prefixWord ++ tailWord_2818720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2818733 : List Nat := [1, 5, 2, 1, 1, 3, 1, 1, 4, 4]
def baseStart_2818733 : Nat := 118140960795 + 2818733 * 2 ^ 59
def prefixEnd_2818733 : Nat := 4983230072969 + 3 ^ 40 * 2818733 * 2
def baseEnd_2818733 : Nat := 482454955229941809291463

theorem tailTrace_2818733 : CollatzResearch.WordTrace tailWord_2818733 prefixEnd_2818733 482454955229941809291463 := by
  unfold tailWord_2818733
  simp only [CollatzResearch.WordTrace]
  refine ⟨102807638497219217115196853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68538425664812811410131235 102807638497219217115196853)
  ·
    refine ⟨9638216109114301604549705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 102807638497219217115196853 9638216109114301604549705)
    ·
      refine ⟨7228662081835726203412279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9638216109114301604549705 7228662081835726203412279)
      ·
        refine ⟨10842993122753589305118419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7228662081835726203412279 10842993122753589305118419)
        ·
          refine ⟨16264489684130383957677629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10842993122753589305118419 16264489684130383957677629)
          ·
            refine ⟨6099183631548893984129111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16264489684130383957677629 6099183631548893984129111)
            ·
              refine ⟨9148775447323340976193667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6099183631548893984129111 9148775447323340976193667)
              ·
                refine ⟨13723163170985011464290501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9148775447323340976193667 13723163170985011464290501)
                ·
                  refine ⟨2573093094559689649554469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13723163170985011464290501 2573093094559689649554469)
                  ·
                    refine ⟨482454955229941809291463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2573093094559689649554469 482454955229941809291463)
                    ·
                      rfl

theorem cell23_2818733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 1, 1, 4, 4].length) (baseStart_2818733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2818733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2818733 prefixEnd_2818733 := by exact prefixLift 2818733
  have htrace : WordTrace (prefixWord ++ tailWord_2818733) baseStart_2818733 baseEnd_2818733 := by
    simpa [prefixWord, tailWord_2818733, baseEnd_2818733] using wordTrace_append hprefix tailTrace_2818733
  have hstable : (prefixWord ++ tailWord_2818733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2818733).length < 2 ^ (prefixWord ++ tailWord_2818733).sum := by decide
  have hdescent : baseEnd_2818733 < baseStart_2818733 := by decide
  rcases family_descends (prefixWord ++ tailWord_2818733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2818750 : List Nat := [4, 2, 1, 1, 2, 1, 5, 1, 2, 4]
def baseStart_2818750 : Nat := 118140960795 + 2818750 * 2 ^ 59
def prefixEnd_2818750 : Nat := 4983230072969 + 3 ^ 40 * 2818750 * 2
def baseEnd_2818750 : Nat := 482457864953650620453937

theorem tailTrace_2818750 : CollatzResearch.WordTrace tailWord_2818750 prefixEnd_2818750 482457864953650620453937 := by
  unfold tailWord_2818750
  simp only [CollatzResearch.WordTrace]
  refine ⟨12851032317269703627320713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68538839025438419345710469 12851032317269703627320713)
  ·
    refine ⟨9638274237952277720490535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12851032317269703627320713 9638274237952277720490535)
    ·
      refine ⟨14457411356928416580735803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9638274237952277720490535 14457411356928416580735803)
      ·
        refine ⟨21686117035392624871103705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14457411356928416580735803 21686117035392624871103705)
        ·
          refine ⟨16264587776544468653327779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21686117035392624871103705 16264587776544468653327779)
          ·
            refine ⟨24396881664816702979991669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16264587776544468653327779 24396881664816702979991669)
            ·
              refine ⟨2287207656076565904374219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24396881664816702979991669 2287207656076565904374219)
              ·
                refine ⟨3430811484114848856561329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2287207656076565904374219 3430811484114848856561329)
                ·
                  refine ⟨2573108613086136642420997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3430811484114848856561329 2573108613086136642420997)
                  ·
                    refine ⟨482457864953650620453937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2573108613086136642420997 482457864953650620453937)
                    ·
                      rfl

theorem cell23_2818750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 5, 1, 2, 4].length) (baseStart_2818750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2818750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2818750 prefixEnd_2818750 := by exact prefixLift 2818750
  have htrace : WordTrace (prefixWord ++ tailWord_2818750) baseStart_2818750 baseEnd_2818750 := by
    simpa [prefixWord, tailWord_2818750, baseEnd_2818750] using wordTrace_append hprefix tailTrace_2818750
  have hstable : (prefixWord ++ tailWord_2818750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2818750).length < 2 ^ (prefixWord ++ tailWord_2818750).sum := by decide
  have hdescent : baseEnd_2818750 < baseStart_2818750 := by decide
  rcases family_descends (prefixWord ++ tailWord_2818750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2818769 : List Nat := [1, 2, 2, 1, 2, 3, 1, 1, 1, 4, 5]
def baseStart_2818769 : Nat := 118140960795 + 2818769 * 2 ^ 59
def prefixEnd_2818769 : Nat := 4983230072969 + 3 ^ 40 * 2818769 * 2
def baseEnd_2818769 : Nat := 1447383350993387287024223

theorem tailTrace_2818769 : CollatzResearch.WordTrace tailWord_2818769 prefixEnd_2818769 1447383350993387287024223 := by
  unfold tailWord_2818769
  simp only [CollatzResearch.WordTrace]
  refine ⟨102808951525088795263507361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68539301016725863509004907 102808951525088795263507361)
  ·
    refine ⟨77106713643816596447630521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102808951525088795263507361 77106713643816596447630521)
    ·
      refine ⟨57830035232862447335722891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77106713643816596447630521 57830035232862447335722891)
      ·
        refine ⟨86745052849293671003584337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57830035232862447335722891 86745052849293671003584337)
        ·
          refine ⟨65058789636970253252688253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86745052849293671003584337 65058789636970253252688253)
          ·
            refine ⟨24397046113863844969758095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65058789636970253252688253 24397046113863844969758095)
            ·
              refine ⟨36595569170795767454637143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24397046113863844969758095 36595569170795767454637143)
              ·
                refine ⟨54893353756193651181955715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36595569170795767454637143 54893353756193651181955715)
                ·
                  refine ⟨82340030634290476772933573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54893353756193651181955715 82340030634290476772933573)
                  ·
                    refine ⟨15438755743929464394925045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 82340030634290476772933573 15438755743929464394925045)
                    ·
                      refine ⟨1447383350993387287024223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15438755743929464394925045 1447383350993387287024223)
                      ·
                        rfl

theorem cell23_2818769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 1, 1, 4, 5].length) (baseStart_2818769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2818769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2818769 prefixEnd_2818769 := by exact prefixLift 2818769
  have htrace : WordTrace (prefixWord ++ tailWord_2818769) baseStart_2818769 baseEnd_2818769 := by
    simpa [prefixWord, tailWord_2818769, baseEnd_2818769] using wordTrace_append hprefix tailTrace_2818769
  have hstable : (prefixWord ++ tailWord_2818769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2818769).length < 2 ^ (prefixWord ++ tailWord_2818769).sum := by decide
  have hdescent : baseEnd_2818769 < baseStart_2818769 := by decide
  rcases family_descends (prefixWord ++ tailWord_2818769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2818779 : List Nat := [1, 1, 1, 1, 1, 1, 1, 3, 6, 3, 4]
def baseStart_2818779 : Nat := 118140960795 + 2818779 * 2 ^ 59
def prefixEnd_2818779 : Nat := 4983230072969 + 3 ^ 40 * 2818779 * 2
def baseEnd_2818779 : Nat := 1447388485799932247899177

theorem tailTrace_2818779 : CollatzResearch.WordTrace tailWord_2818779 prefixEnd_2818779 1447388485799932247899177 := by
  unfold tailWord_2818779
  simp only [CollatzResearch.WordTrace]
  refine ⟨102809316255052566971371391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68539544170035044647580927 102809316255052566971371391)
  ·
    refine ⟨154213974382578850457057087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102809316255052566971371391 154213974382578850457057087)
    ·
      refine ⟨231320961573868275685585631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154213974382578850457057087 231320961573868275685585631)
      ·
        refine ⟨346981442360802413528378447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 231320961573868275685585631 346981442360802413528378447)
        ·
          refine ⟨520472163541203620292567671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 346981442360802413528378447 520472163541203620292567671)
          ·
            refine ⟨780708245311805430438851507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 520472163541203620292567671 780708245311805430438851507)
            ·
              refine ⟨1171062367967708145658277261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 780708245311805430438851507 1171062367967708145658277261)
              ·
                refine ⟨439148387987890554621853973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1171062367967708145658277261 439148387987890554621853973)
                ·
                  refine ⟨20585080686932369747899405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 439148387987890554621853973 20585080686932369747899405)
                  ·
                    refine ⟨7719405257599638655462277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20585080686932369747899405 7719405257599638655462277)
                    ·
                      refine ⟨1447388485799932247899177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7719405257599638655462277 1447388485799932247899177)
                      ·
                        rfl

theorem cell23_2818779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 6, 3, 4].length) (baseStart_2818779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2818779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2818779 prefixEnd_2818779 := by exact prefixLift 2818779
  have htrace : WordTrace (prefixWord ++ tailWord_2818779) baseStart_2818779 baseEnd_2818779 := by
    simpa [prefixWord, tailWord_2818779, baseEnd_2818779] using wordTrace_append hprefix tailTrace_2818779
  have hstable : (prefixWord ++ tailWord_2818779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2818779).length < 2 ^ (prefixWord ++ tailWord_2818779).sum := by decide
  have hdescent : baseEnd_2818779 < baseStart_2818779 := by decide
  rcases family_descends (prefixWord ++ tailWord_2818779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2818806 : List Nat := [5, 1, 1, 1, 1, 2, 2, 1, 1, 8]
def baseStart_2818806 : Nat := 118140960795 + 2818806 * 2 ^ 59
def prefixEnd_2818806 : Nat := 4983230072969 + 3 ^ 40 * 2818806 * 2
def baseEnd_2818806 : Nat := 482467449925867880753851

theorem tailTrace_2818806 : CollatzResearch.WordTrace tailWord_2818806 prefixEnd_2818806 482467449925867880753851 := by
  unfold tailWord_2818806
  simp only [CollatzResearch.WordTrace]
  refine ⟨6425643814122171911412767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 68540200683969833721736181 6425643814122171911412767)
  ·
    refine ⟨9638465721183257867119151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6425643814122171911412767 9638465721183257867119151)
    ·
      refine ⟨14457698581774886800678727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9638465721183257867119151 14457698581774886800678727)
      ·
        refine ⟨21686547872662330201018091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14457698581774886800678727 21686547872662330201018091)
        ·
          refine ⟨32529821808993495301527137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21686547872662330201018091 32529821808993495301527137)
          ·
            refine ⟨24397366356745121476145353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32529821808993495301527137 24397366356745121476145353)
            ·
              refine ⟨18298024767558841107109015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24397366356745121476145353 18298024767558841107109015)
              ·
                refine ⟨27447037151338261660663523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18298024767558841107109015 27447037151338261660663523)
                ·
                  refine ⟨41170555727007392490995285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27447037151338261660663523 41170555727007392490995285)
                  ·
                    refine ⟨482467449925867880753851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 41170555727007392490995285 482467449925867880753851)
                    ·
                      rfl

theorem cell23_2818806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 1, 1, 8].length) (baseStart_2818806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2818806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2818806 prefixEnd_2818806 := by exact prefixLift 2818806
  have htrace : WordTrace (prefixWord ++ tailWord_2818806) baseStart_2818806 baseEnd_2818806 := by
    simpa [prefixWord, tailWord_2818806, baseEnd_2818806] using wordTrace_append hprefix tailTrace_2818806
  have hstable : (prefixWord ++ tailWord_2818806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2818806).length < 2 ^ (prefixWord ++ tailWord_2818806).sum := by decide
  have hdescent : baseEnd_2818806 < baseStart_2818806 := by decide
  rcases family_descends (prefixWord ++ tailWord_2818806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2818809 : List Nat := [1, 2, 1, 3, 1, 1, 1, 2, 2, 3, 6]
def baseStart_2818809 : Nat := 118140960795 + 2818809 * 2 ^ 59
def prefixEnd_2818809 : Nat := 4983230072969 + 3 ^ 40 * 2818809 * 2
def baseEnd_2818809 : Nat := 1447403890219567130524039

theorem tailTrace_2818809 : CollatzResearch.WordTrace tailWord_2818809 prefixEnd_2818809 1447403890219567130524039 := by
  unfold tailWord_2818809
  simp only [CollatzResearch.WordTrace]
  refine ⟨102810410444943882094963481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68540273629962588063308987 102810410444943882094963481)
  ·
    refine ⟨77107807833707911571222611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102810410444943882094963481 77107807833707911571222611)
    ·
      refine ⟨115661711750561867356833917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77107807833707911571222611 115661711750561867356833917)
      ·
        refine ⟨43373141906460700258812719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 115661711750561867356833917 43373141906460700258812719)
        ·
          refine ⟨65059712859691050388219079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43373141906460700258812719 65059712859691050388219079)
          ·
            refine ⟨97589569289536575582328619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65059712859691050388219079 97589569289536575582328619)
            ·
              refine ⟨146384353934304863373492929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97589569289536575582328619 146384353934304863373492929)
              ·
                refine ⟨109788265450728647530119697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 146384353934304863373492929 109788265450728647530119697)
                ·
                  refine ⟨82341199088046485647589773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 109788265450728647530119697 82341199088046485647589773)
                  ·
                    refine ⟨30877949658017432117846165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 82341199088046485647589773 30877949658017432117846165)
                    ·
                      refine ⟨1447403890219567130524039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 30877949658017432117846165 1447403890219567130524039)
                      ·
                        rfl

theorem cell23_2818809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 2, 2, 3, 6].length) (baseStart_2818809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2818809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2818809 prefixEnd_2818809 := by exact prefixLift 2818809
  have htrace : WordTrace (prefixWord ++ tailWord_2818809) baseStart_2818809 baseEnd_2818809 := by
    simpa [prefixWord, tailWord_2818809, baseEnd_2818809] using wordTrace_append hprefix tailTrace_2818809
  have hstable : (prefixWord ++ tailWord_2818809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2818809).length < 2 ^ (prefixWord ++ tailWord_2818809).sum := by decide
  have hdescent : baseEnd_2818809 < baseStart_2818809 := by decide
  rcases family_descends (prefixWord ++ tailWord_2818809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2818813 : List Nat := [1, 4, 1, 1, 1, 1, 4, 3, 1, 4, 2]
def baseStart_2818813 : Nat := 118140960795 + 2818813 * 2 ^ 59
def prefixEnd_2818813 : Nat := 4983230072969 + 3 ^ 40 * 2818813 * 2
def baseEnd_2818813 : Nat := 1447405944142185114874021

theorem tailTrace_2818813 : CollatzResearch.WordTrace tailWord_2818813 prefixEnd_2818813 1447405944142185114874021 := by
  unfold tailWord_2818813
  simp only [CollatzResearch.WordTrace]
  refine ⟨102810556336929390778109093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68540370891286260518739395 102810556336929390778109093)
  ·
    refine ⟨19276979313174260770895455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 102810556336929390778109093 19276979313174260770895455)
    ·
      refine ⟨28915468969761391156343183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19276979313174260770895455 28915468969761391156343183)
      ·
        refine ⟨43373203454642086734514775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28915468969761391156343183 43373203454642086734514775)
        ·
          refine ⟨65059805181963130101772163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43373203454642086734514775 65059805181963130101772163)
          ·
            refine ⟨97589707772944695152658245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65059805181963130101772163 97589707772944695152658245)
            ·
              refine ⟨18298070207427130341123421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 97589707772944695152658245 18298070207427130341123421)
              ·
                refine ⟨6861776327785173877921283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18298070207427130341123421 6861776327785173877921283)
                ·
                  refine ⟨10292664491677760816881925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6861776327785173877921283 10292664491677760816881925)
                  ·
                    refine ⟨1929874592189580153165361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10292664491677760816881925 1929874592189580153165361)
                    ·
                      refine ⟨1447405944142185114874021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1929874592189580153165361 1447405944142185114874021)
                      ·
                        rfl

theorem cell23_2818813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 3, 1, 4, 2].length) (baseStart_2818813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2818813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2818813 prefixEnd_2818813 := by exact prefixLift 2818813
  have htrace : WordTrace (prefixWord ++ tailWord_2818813) baseStart_2818813 baseEnd_2818813 := by
    simpa [prefixWord, tailWord_2818813, baseEnd_2818813] using wordTrace_append hprefix tailTrace_2818813
  have hstable : (prefixWord ++ tailWord_2818813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2818813).length < 2 ^ (prefixWord ++ tailWord_2818813).sum := by decide
  have hdescent : baseEnd_2818813 < baseStart_2818813 := by decide
  rcases family_descends (prefixWord ++ tailWord_2818813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2818819 : List Nat := [1, 1, 1, 3, 2, 2, 1, 3, 9]
def baseStart_2818819 : Nat := 118140960795 + 2818819 * 2 ^ 59
def prefixEnd_2818819 : Nat := 4983230072969 + 3 ^ 40 * 2818819 * 2
def baseEnd_2818819 : Nat := 160823225002901343488777

theorem tailTrace_2818819 : CollatzResearch.WordTrace tailWord_2818819 prefixEnd_2818819 160823225002901343488777 := by
  unfold tailWord_2818819
  simp only [CollatzResearch.WordTrace]
  refine ⟨102810775174907653802827511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68540516783271769201885007 102810775174907653802827511)
  ·
    refine ⟨154216162762361480704241267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102810775174907653802827511 154216162762361480704241267)
    ·
      refine ⟨231324244143542221056361901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154216162762361480704241267 231324244143542221056361901)
      ·
        refine ⟨86746591553828332896135713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 231324244143542221056361901 86746591553828332896135713)
        ·
          refine ⟨65059943665371249672101785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86746591553828332896135713 65059943665371249672101785)
          ·
            refine ⟨48794957749028437254076339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65059943665371249672101785 48794957749028437254076339)
            ·
              refine ⟨73192436623542655881114509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48794957749028437254076339 73192436623542655881114509)
              ·
                refine ⟨27447163733828495955417941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 73192436623542655881114509 27447163733828495955417941)
                ·
                  refine ⟨160823225002901343488777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 27447163733828495955417941 160823225002901343488777)
                  ·
                    rfl

theorem cell23_2818819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 3, 9].length) (baseStart_2818819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2818819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2818819 prefixEnd_2818819 := by exact prefixLift 2818819
  have htrace : WordTrace (prefixWord ++ tailWord_2818819) baseStart_2818819 baseEnd_2818819 := by
    simpa [prefixWord, tailWord_2818819, baseEnd_2818819] using wordTrace_append hprefix tailTrace_2818819
  have hstable : (prefixWord ++ tailWord_2818819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2818819).length < 2 ^ (prefixWord ++ tailWord_2818819).sum := by decide
  have hdescent : baseEnd_2818819 < baseStart_2818819 := by decide
  rcases family_descends (prefixWord ++ tailWord_2818819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2818847 : List Nat := [1, 1, 2, 4, 2, 3, 2, 2, 2, 2, 2]
def baseStart_2818847 : Nat := 118140960795 + 2818847 * 2 ^ 59
def prefixEnd_2818847 : Nat := 4983230072969 + 3 ^ 40 * 2818847 * 2
def baseEnd_2818847 : Nat := 1447423402484437981848865

theorem tailTrace_2818847 : CollatzResearch.WordTrace tailWord_2818847 prefixEnd_2818847 1447423402484437981848865 := by
  unfold tailWord_2818847
  simp only [CollatzResearch.WordTrace]
  refine ⟨102811796418806214584846795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68541197612537476389897863 102811796418806214584846795)
  ·
    refine ⟨154217694628209321877270193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102811796418806214584846795 154217694628209321877270193)
    ·
      refine ⟨115663270971156991407952645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154217694628209321877270193 115663270971156991407952645)
      ·
        refine ⟨21686863307091935888991121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 115663270971156991407952645 21686863307091935888991121)
        ·
          refine ⟨16265147480318951916743341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21686863307091935888991121 16265147480318951916743341)
          ·
            refine ⟨6099430305119606968778753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16265147480318951916743341 6099430305119606968778753)
            ·
              refine ⟨4574572728839705226584065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6099430305119606968778753 4574572728839705226584065)
              ·
                refine ⟨3430929546629778919938049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4574572728839705226584065 3430929546629778919938049)
                ·
                  refine ⟨2573197159972334189953537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3430929546629778919938049 2573197159972334189953537)
                  ·
                    refine ⟨1929897869979250642465153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2573197159972334189953537 1929897869979250642465153)
                    ·
                      refine ⟨1447423402484437981848865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1929897869979250642465153 1447423402484437981848865)
                      ·
                        rfl

theorem cell23_2818847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 2, 2, 2, 2, 2].length) (baseStart_2818847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2818847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2818847 prefixEnd_2818847 := by exact prefixLift 2818847
  have htrace : WordTrace (prefixWord ++ tailWord_2818847) baseStart_2818847 baseEnd_2818847 := by
    simpa [prefixWord, tailWord_2818847, baseEnd_2818847] using wordTrace_append hprefix tailTrace_2818847
  have hstable : (prefixWord ++ tailWord_2818847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2818847).length < 2 ^ (prefixWord ++ tailWord_2818847).sum := by decide
  have hdescent : baseEnd_2818847 < baseStart_2818847 := by decide
  rcases family_descends (prefixWord ++ tailWord_2818847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2818853 : List Nat := [1, 3, 1, 2, 3, 1, 3, 4, 5]
def baseStart_2818853 : Nat := 118140960795 + 2818853 * 2 ^ 59
def prefixEnd_2818853 : Nat := 4983230072969 + 3 ^ 40 * 2818853 * 2
def baseEnd_2818853 : Nat := 160825164818707217597093

theorem tailTrace_2818853 : CollatzResearch.WordTrace tailWord_2818853 prefixEnd_2818853 160825164818707217597093 := by
  unfold tailWord_2818853
  simp only [CollatzResearch.WordTrace]
  refine ⟨102812015256784477609565213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68541343504522985073043475 102812015256784477609565213)
  ·
    refine ⟨38554505721294179103586955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102812015256784477609565213 38554505721294179103586955)
    ·
      refine ⟨57831758581941268655380433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38554505721294179103586955 57831758581941268655380433)
      ·
        refine ⟨43373818936455951491535325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57831758581941268655380433 43373818936455951491535325)
        ·
          refine ⟨16265182101170981809325747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43373818936455951491535325 16265182101170981809325747)
          ·
            refine ⟨24397773151756472713988621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16265182101170981809325747 24397773151756472713988621)
            ·
              refine ⟨9149164931908677267745733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24397773151756472713988621 9149164931908677267745733)
              ·
                refine ⟨1715468424732876987702325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9149164931908677267745733 1715468424732876987702325)
                ·
                  refine ⟨160825164818707217597093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1715468424732876987702325 160825164818707217597093)
                  ·
                    rfl

theorem cell23_2818853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 3, 4, 5].length) (baseStart_2818853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2818853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2818853 prefixEnd_2818853 := by exact prefixLift 2818853
  have htrace : WordTrace (prefixWord ++ tailWord_2818853) baseStart_2818853 baseEnd_2818853 := by
    simpa [prefixWord, tailWord_2818853, baseEnd_2818853] using wordTrace_append hprefix tailTrace_2818853
  have hstable : (prefixWord ++ tailWord_2818853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2818853).length < 2 ^ (prefixWord ++ tailWord_2818853).sum := by decide
  have hdescent : baseEnd_2818853 < baseStart_2818853 := by decide
  rcases family_descends (prefixWord ++ tailWord_2818853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2818866 : List Nat := [3, 2, 1, 1, 3, 1, 2, 2, 1, 7]
def baseStart_2818866 : Nat := 118140960795 + 2818866 * 2 ^ 59
def prefixEnd_2818866 : Nat := 4983230072969 + 3 ^ 40 * 2818866 * 2
def baseEnd_2818866 : Nat := 482477719538957802503759

theorem tailTrace_2818866 : CollatzResearch.WordTrace tailWord_2818866 prefixEnd_2818866 482477719538957802503759 := by
  unfold tailWord_2818866
  simp only [CollatzResearch.WordTrace]
  refine ⟨25703122351434345207447113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68541659603824920553192301 25703122351434345207447113)
  ·
    refine ⟨19277341763575758905585335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25703122351434345207447113 19277341763575758905585335)
    ·
      refine ⟨28916012645363638358378003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19277341763575758905585335 28916012645363638358378003)
      ·
        refine ⟨43374018968045457537567005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28916012645363638358378003 43374018968045457537567005)
        ·
          refine ⟨16265257113017046576587627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43374018968045457537567005 16265257113017046576587627)
          ·
            refine ⟨24397885669525569864881441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16265257113017046576587627 24397885669525569864881441)
            ·
              refine ⟨18298414252144177398661081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24397885669525569864881441 18298414252144177398661081)
              ·
                refine ⟨13723810689108133048995811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18298414252144177398661081 13723810689108133048995811)
                ·
                  refine ⟨20585716033662199573493717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13723810689108133048995811 20585716033662199573493717)
                  ·
                    refine ⟨482477719538957802503759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 20585716033662199573493717 482477719538957802503759)
                    ·
                      rfl

theorem cell23_2818866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 2, 1, 7].length) (baseStart_2818866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2818866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2818866 prefixEnd_2818866 := by exact prefixLift 2818866
  have htrace : WordTrace (prefixWord ++ tailWord_2818866) baseStart_2818866 baseEnd_2818866 := by
    simpa [prefixWord, tailWord_2818866, baseEnd_2818866] using wordTrace_append hprefix tailTrace_2818866
  have hstable : (prefixWord ++ tailWord_2818866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2818866).length < 2 ^ (prefixWord ++ tailWord_2818866).sum := by decide
  have hdescent : baseEnd_2818866 < baseStart_2818866 := by decide
  rcases family_descends (prefixWord ++ tailWord_2818866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2818870 : List Nat := [5, 1, 2, 2, 2, 1, 1, 2, 7]
def baseStart_2818870 : Nat := 118140960795 + 2818870 * 2 ^ 59
def prefixEnd_2818870 : Nat := 4983230072969 + 3 ^ 40 * 2818870 * 2
def baseEnd_2818870 : Nat := 160826134726610154651251

theorem tailTrace_2818870 : CollatzResearch.WordTrace tailWord_2818870 prefixEnd_2818870 160826134726610154651251 := by
  unfold tailWord_2818870
  simp only [CollatzResearch.WordTrace]
  refine ⟨6425789706107680594558379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 68541756865148593008622709 6425789706107680594558379)
  ·
    refine ⟨9638684559161520891837569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6425789706107680594558379 9638684559161520891837569)
    ·
      refine ⟨7229013419371140668878177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9638684559161520891837569 7229013419371140668878177)
      ·
        refine ⟨5421760064528355501658633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7229013419371140668878177 5421760064528355501658633)
        ·
          refine ⟨4066320048396266626243975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5421760064528355501658633 4066320048396266626243975)
          ·
            refine ⟨6099480072594399939365963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4066320048396266626243975 6099480072594399939365963)
            ·
              refine ⟨9149220108891599909048945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6099480072594399939365963 9149220108891599909048945)
              ·
                refine ⟨6861915081668699931786709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9149220108891599909048945 6861915081668699931786709)
                ·
                  refine ⟨160826134726610154651251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6861915081668699931786709 160826134726610154651251)
                  ·
                    rfl

theorem cell23_2818870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 1, 2, 7].length) (baseStart_2818870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2818870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2818870 prefixEnd_2818870 := by exact prefixLift 2818870
  have htrace : WordTrace (prefixWord ++ tailWord_2818870) baseStart_2818870 baseEnd_2818870 := by
    simpa [prefixWord, tailWord_2818870, baseEnd_2818870] using wordTrace_append hprefix tailTrace_2818870
  have hstable : (prefixWord ++ tailWord_2818870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2818870).length < 2 ^ (prefixWord ++ tailWord_2818870).sum := by decide
  have hdescent : baseEnd_2818870 < baseStart_2818870 := by decide
  rcases family_descends (prefixWord ++ tailWord_2818870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2818920 : List Nat := [2, 1, 4, 2, 1, 2, 2, 1, 2, 4, 2]
def baseStart_2818920 : Nat := 118140960795 + 2818920 * 2 ^ 59
def prefixEnd_2818920 : Nat := 4983230072969 + 3 ^ 40 * 2818920 * 2
def baseEnd_2818920 : Nat := 1447460886572216196236029

theorem tailTrace_2818920 : CollatzResearch.WordTrace tailWord_2818920 prefixEnd_2818920 1447460886572216196236029 := by
  unfold tailWord_2818920
  simp only [CollatzResearch.WordTrace]
  refine ⟨51407229473770874026127107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68542972631694498701502809 51407229473770874026127107)
  ·
    refine ⟨77110844210656311039190661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51407229473770874026127107 77110844210656311039190661)
    ·
      refine ⟨14458283289498058319848249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 77110844210656311039190661 14458283289498058319848249)
      ·
        refine ⟨10843712467123543739886187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14458283289498058319848249 10843712467123543739886187)
        ·
          refine ⟨16265568700685315609829281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10843712467123543739886187 16265568700685315609829281)
          ·
            refine ⟨12199176525513986707371961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16265568700685315609829281 12199176525513986707371961)
            ·
              refine ⟨9149382394135490030528971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12199176525513986707371961 9149382394135490030528971)
              ·
                refine ⟨13724073591203235045793457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9149382394135490030528971 13724073591203235045793457)
                ·
                  refine ⟨10293055193402426284345093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13724073591203235045793457 10293055193402426284345093)
                  ·
                    refine ⟨1929947848762954928314705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10293055193402426284345093 1929947848762954928314705)
                    ·
                      refine ⟨1447460886572216196236029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1929947848762954928314705 1447460886572216196236029)
                      ·
                        rfl

theorem cell23_2818920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 2, 1, 2, 4, 2].length) (baseStart_2818920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2818920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2818920 prefixEnd_2818920 := by exact prefixLift 2818920
  have htrace : WordTrace (prefixWord ++ tailWord_2818920) baseStart_2818920 baseEnd_2818920 := by
    simpa [prefixWord, tailWord_2818920, baseEnd_2818920] using wordTrace_append hprefix tailTrace_2818920
  have hstable : (prefixWord ++ tailWord_2818920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2818920).length < 2 ^ (prefixWord ++ tailWord_2818920).sum := by decide
  have hdescent : baseEnd_2818920 < baseStart_2818920 := by decide
  rcases family_descends (prefixWord ++ tailWord_2818920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2818963 : List Nat := [1, 1, 1, 2, 1, 2, 1, 4, 3, 5, 2]
def baseStart_2818963 : Nat := 118140960795 + 2818963 * 2 ^ 59
def prefixEnd_2818963 : Nat := 4983230072969 + 3 ^ 40 * 2818963 * 2
def baseEnd_2818963 : Nat := 1447482966240359527998331

theorem tailTrace_2818963 : CollatzResearch.WordTrace tailWord_2818963 prefixEnd_2818963 1447482966240359527998331 := by
  unfold tailWord_2818963
  simp only [CollatzResearch.WordTrace]
  refine ⟨102816027286385966396069543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68544018190923977597379695 102816027286385966396069543)
  ·
    refine ⟨154224040929578949594104315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102816027286385966396069543 154224040929578949594104315)
    ·
      refine ⟨231336061394368424391156473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154224040929578949594104315 231336061394368424391156473)
      ·
        refine ⟨173502046045776318293367355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 231336061394368424391156473 173502046045776318293367355)
        ·
          refine ⟨260253069068664477440051033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173502046045776318293367355 260253069068664477440051033)
          ·
            refine ⟨195189801801498358080038275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 260253069068664477440051033 195189801801498358080038275)
            ·
              refine ⟨292784702702247537120057413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 195189801801498358080038275 292784702702247537120057413)
              ·
                refine ⟨54897131756671413210010765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 292784702702247537120057413 54897131756671413210010765)
                ·
                  refine ⟨20586424408751779953754037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54897131756671413210010765 20586424408751779953754037)
                  ·
                    refine ⟨1929977288320479370664441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 20586424408751779953754037 1929977288320479370664441)
                    ·
                      refine ⟨1447482966240359527998331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1929977288320479370664441 1447482966240359527998331)
                      ·
                        rfl

theorem cell23_2818963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 4, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 4, 3, 5, 2].length) (baseStart_2818963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2818963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2818963 prefixEnd_2818963 := by exact prefixLift 2818963
  have htrace : WordTrace (prefixWord ++ tailWord_2818963) baseStart_2818963 baseEnd_2818963 := by
    simpa [prefixWord, tailWord_2818963, baseEnd_2818963] using wordTrace_append hprefix tailTrace_2818963
  have hstable : (prefixWord ++ tailWord_2818963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2818963).length < 2 ^ (prefixWord ++ tailWord_2818963).sum := by decide
  have hdescent : baseEnd_2818963 < baseStart_2818963 := by decide
  rcases family_descends (prefixWord ++ tailWord_2818963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2818964 : List Nat := [2, 4, 2, 1, 1, 1, 5, 2, 1, 4]
def baseStart_2818964 : Nat := 118140960795 + 2818964 * 2 ^ 59
def prefixEnd_2818964 : Nat := 4983230072969 + 3 ^ 40 * 2818964 * 2
def baseEnd_2818964 : Nat := 482494493240338008028609

theorem tailTrace_2818964 : CollatzResearch.WordTrace tailWord_2818964 prefixEnd_2818964 482494493240338008028609 := by
  unfold tailWord_2818964
  simp only [CollatzResearch.WordTrace]
  refine ⟨51408031879691171783427973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68544042506254895711237297 51408031879691171783427973)
  ·
    refine ⟨9639005977442094709392745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51408031879691171783427973 9639005977442094709392745)
    ·
      refine ⟨7229254483081571032044559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9639005977442094709392745 7229254483081571032044559)
      ·
        refine ⟨10843881724622356548066839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7229254483081571032044559 10843881724622356548066839)
        ·
          refine ⟨16265822586933534822100259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10843881724622356548066839 16265822586933534822100259)
          ·
            refine ⟨24398733880400302233150389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16265822586933534822100259 24398733880400302233150389)
            ·
              refine ⟨2287381301287528334357849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24398733880400302233150389 2287381301287528334357849)
              ·
                refine ⟨1715535975965646250768387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2287381301287528334357849 1715535975965646250768387)
                ·
                  refine ⟨2573303963948469376152581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1715535975965646250768387 2573303963948469376152581)
                  ·
                    refine ⟨482494493240338008028609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2573303963948469376152581 482494493240338008028609)
                    ·
                      rfl

theorem cell23_2818964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 5, 2, 1, 4].length) (baseStart_2818964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2818964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2818964 prefixEnd_2818964 := by exact prefixLift 2818964
  have htrace : WordTrace (prefixWord ++ tailWord_2818964) baseStart_2818964 baseEnd_2818964 := by
    simpa [prefixWord, tailWord_2818964, baseEnd_2818964] using wordTrace_append hprefix tailTrace_2818964
  have hstable : (prefixWord ++ tailWord_2818964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2818964).length < 2 ^ (prefixWord ++ tailWord_2818964).sum := by decide
  have hdescent : baseEnd_2818964 < baseStart_2818964 := by decide
  rcases family_descends (prefixWord ++ tailWord_2818964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2818973 : List Nat := [1, 4, 2, 1, 2, 1, 2, 2, 3, 5]
def baseStart_2818973 : Nat := 118140960795 + 2818973 * 2 ^ 59
def prefixEnd_2818973 : Nat := 4983230072969 + 3 ^ 40 * 2818973 * 2
def baseEnd_2818973 : Nat := 482496033682301496291095

theorem tailTrace_2818973 : CollatzResearch.WordTrace tailWord_2818973 prefixEnd_2818973 482496033682301496291095 := by
  unfold tailWord_2818973
  simp only [CollatzResearch.WordTrace]
  refine ⟨102816392016349738103933573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68544261344233158735955715 102816392016349738103933573)
  ·
    refine ⟨19278073503065575894487545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 102816392016349738103933573 19278073503065575894487545)
    ·
      refine ⟨14458555127299181920865659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19278073503065575894487545 14458555127299181920865659)
      ·
        refine ⟨21687832690948772881298489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14458555127299181920865659 21687832690948772881298489)
        ·
          refine ⟨16265874518211579660973867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21687832690948772881298489 16265874518211579660973867)
          ·
            refine ⟨24398811777317369491460801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16265874518211579660973867 24398811777317369491460801)
            ·
              refine ⟨18299108832988027118595601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24398811777317369491460801 18299108832988027118595601)
              ·
                refine ⟨13724331624741020338946701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18299108832988027118595601 13724331624741020338946701)
                ·
                  refine ⟨5146624359277882627105013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13724331624741020338946701 5146624359277882627105013)
                  ·
                    refine ⟨482496033682301496291095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5146624359277882627105013 482496033682301496291095)
                    ·
                      rfl

theorem cell23_2818973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 2, 3, 5].length) (baseStart_2818973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2818973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2818973 prefixEnd_2818973 := by exact prefixLift 2818973
  have htrace : WordTrace (prefixWord ++ tailWord_2818973) baseStart_2818973 baseEnd_2818973 := by
    simpa [prefixWord, tailWord_2818973, baseEnd_2818973] using wordTrace_append hprefix tailTrace_2818973
  have hstable : (prefixWord ++ tailWord_2818973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2818973).length < 2 ^ (prefixWord ++ tailWord_2818973).sum := by decide
  have hdescent : baseEnd_2818973 < baseStart_2818973 := by decide
  rcases family_descends (prefixWord ++ tailWord_2818973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2818977 : List Nat := [1, 2, 3, 4, 1, 3, 2, 1, 6]
def baseStart_2818977 : Nat := 118140960795 + 2818977 * 2 ^ 59
def prefixEnd_2818977 : Nat := 4983230072969 + 3 ^ 40 * 2818977 * 2
def baseEnd_2818977 : Nat := 160832239441058052580363

theorem tailTrace_2818977 : CollatzResearch.WordTrace tailWord_2818977 prefixEnd_2818977 160832239441058052580363 := by
  unfold tailWord_2818977
  simp only [CollatzResearch.WordTrace]
  refine ⟨102816537908335246787079185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68544358605556831191386123 102816537908335246787079185)
  ·
    refine ⟨77112403431251435090309389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102816537908335246787079185 77112403431251435090309389)
    ·
      refine ⟨28917151286719288158866021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77112403431251435090309389 28917151286719288158866021)
      ·
        refine ⟨5421965866259866529787379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28917151286719288158866021 5421965866259866529787379)
        ·
          refine ⟨8132948799389799794681069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5421965866259866529787379 8132948799389799794681069)
          ·
            refine ⟨3049855799771174923005401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8132948799389799794681069 3049855799771174923005401)
            ·
              refine ⟨2287391849828381192254051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3049855799771174923005401 2287391849828381192254051)
              ·
                refine ⟨3431087774742571788381077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2287391849828381192254051 3431087774742571788381077)
                ·
                  refine ⟨160832239441058052580363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3431087774742571788381077 160832239441058052580363)
                  ·
                    rfl

theorem cell23_2818977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 2, 1, 6].length) (baseStart_2818977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2818977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2818977 prefixEnd_2818977 := by exact prefixLift 2818977
  have htrace : WordTrace (prefixWord ++ tailWord_2818977) baseStart_2818977 baseEnd_2818977 := by
    simpa [prefixWord, tailWord_2818977, baseEnd_2818977] using wordTrace_append hprefix tailTrace_2818977
  have hstable : (prefixWord ++ tailWord_2818977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2818977).length < 2 ^ (prefixWord ++ tailWord_2818977).sum := by decide
  have hdescent : baseEnd_2818977 < baseStart_2818977 := by decide
  rcases family_descends (prefixWord ++ tailWord_2818977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2818980 : List Nat := [2, 3, 1, 2, 1, 2, 1, 2, 4, 3, 2]
def baseStart_2818980 : Nat := 118140960795 + 2818980 * 2 ^ 59
def prefixEnd_2818980 : Nat := 4983230072969 + 3 ^ 40 * 2818980 * 2
def baseEnd_2818980 : Nat := 1447491695411485961485753

theorem tailTrace_2818980 : CollatzResearch.WordTrace tailWord_2818980 prefixEnd_2818980 1447491695411485961485753 := by
  unfold tailWord_2818980
  simp only [CollatzResearch.WordTrace]
  refine ⟨51408323663662189149719197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68544431551549585532958929 51408323663662189149719197)
  ·
    refine ⟨19278121373873320931144699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51408323663662189149719197 19278121373873320931144699)
    ·
      refine ⟨28917182060809981396717049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19278121373873320931144699 28917182060809981396717049)
      ·
        refine ⟨21687886545607486047537787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28917182060809981396717049 21687886545607486047537787)
        ·
          refine ⟨32531829818411229071306681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21687886545607486047537787 32531829818411229071306681)
          ·
            refine ⟨24398872363808421803480011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32531829818411229071306681 24398872363808421803480011)
            ·
              refine ⟨36598308545712632705220017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24398872363808421803480011 36598308545712632705220017)
              ·
                refine ⟨27448731409284474528915013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36598308545712632705220017 27448731409284474528915013)
                ·
                  refine ⟨5146637139240838974171565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27448731409284474528915013 5146637139240838974171565)
                  ·
                    refine ⟨1929988927215314615314337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5146637139240838974171565 1929988927215314615314337)
                    ·
                      refine ⟨1447491695411485961485753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1929988927215314615314337 1447491695411485961485753)
                      ·
                        rfl

theorem cell23_2818980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 2, 4, 3, 2].length) (baseStart_2818980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2818980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2818980 prefixEnd_2818980 := by exact prefixLift 2818980
  have htrace : WordTrace (prefixWord ++ tailWord_2818980) baseStart_2818980 baseEnd_2818980 := by
    simpa [prefixWord, tailWord_2818980, baseEnd_2818980] using wordTrace_append hprefix tailTrace_2818980
  have hstable : (prefixWord ++ tailWord_2818980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2818980).length < 2 ^ (prefixWord ++ tailWord_2818980).sum := by decide
  have hdescent : baseEnd_2818980 < baseStart_2818980 := by decide
  rcases family_descends (prefixWord ++ tailWord_2818980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2818997 : List Nat := [1, 3, 3, 2, 1, 1, 4, 1, 2, 3, 2]
def baseStart_2818997 : Nat := 118140960795 + 2818997 * 2 ^ 59
def prefixEnd_2818997 : Nat := 4983230072969 + 3 ^ 40 * 2818997 * 2
def baseEnd_2818997 : Nat := 1447500424582612394973175

theorem tailTrace_2818997 : CollatzResearch.WordTrace tailWord_2818997 prefixEnd_2818997 1447500424582612394973175 := by
  unfold tailWord_2818997
  simp only [CollatzResearch.WordTrace]
  refine ⟨102817267368262790202807245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68544844912175193468538163 102817267368262790202807245)
  ·
    refine ⟨38556475263098546326052717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102817267368262790202807245 38556475263098546326052717)
    ·
      refine ⟨14458678223661954872269769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38556475263098546326052717 14458678223661954872269769)
      ·
        refine ⟨10844008667746466154202327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14458678223661954872269769 10844008667746466154202327)
        ·
          refine ⟨16266013001619699231303491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10844008667746466154202327 16266013001619699231303491)
          ·
            refine ⟨24399019502429548846955237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16266013001619699231303491 24399019502429548846955237)
            ·
              refine ⟨4574816156705540408804107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24399019502429548846955237 4574816156705540408804107)
              ·
                refine ⟨6862224235058310613206161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4574816156705540408804107 6862224235058310613206161)
                ·
                  refine ⟨5146668176293732959904621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6862224235058310613206161 5146668176293732959904621)
                  ·
                    refine ⟨1930000566110149859964233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5146668176293732959904621 1930000566110149859964233)
                    ·
                      refine ⟨1447500424582612394973175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1930000566110149859964233 1447500424582612394973175)
                      ·
                        rfl

theorem cell23_2818997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 4, 1, 2, 3, 2].length) (baseStart_2818997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2818997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2818997 prefixEnd_2818997 := by exact prefixLift 2818997
  have htrace : WordTrace (prefixWord ++ tailWord_2818997) baseStart_2818997 baseEnd_2818997 := by
    simpa [prefixWord, tailWord_2818997, baseEnd_2818997] using wordTrace_append hprefix tailTrace_2818997
  have hstable : (prefixWord ++ tailWord_2818997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2818997).length < 2 ^ (prefixWord ++ tailWord_2818997).sum := by decide
  have hdescent : baseEnd_2818997 < baseStart_2818997 := by decide
  rcases family_descends (prefixWord ++ tailWord_2818997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2819016 : List Nat := [2, 1, 3, 1, 16]
def baseStart_2819016 : Nat := 118140960795 + 2819016 * 2 ^ 59
def prefixEnd_2819016 : Nat := 4983230072969 + 3 ^ 40 * 2819016 * 2
def baseEnd_2819016 : Nat := 1985610673134496324603

theorem tailTrace_2819016 : CollatzResearch.WordTrace tailWord_2819016 prefixEnd_2819016 1985610673134496324603 := by
  unfold tailWord_2819016
  simp only [CollatzResearch.WordTrace]
  refine ⟨51408980177596978223874451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68545306903462637631832601 51408980177596978223874451)
  ·
    refine ⟨77113470266395467335811677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51408980177596978223874451 77113470266395467335811677)
    ·
      refine ⟨28917551349898300250929379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77113470266395467335811677 28917551349898300250929379)
      ·
        refine ⟨43376327024847450376394069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28917551349898300250929379 43376327024847450376394069)
        ·
          refine ⟨1985610673134496324603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 16 43376327024847450376394069 1985610673134496324603)
          ·
            rfl

theorem cell23_2819016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 16].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 16].length) (baseStart_2819016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2819016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2819016 prefixEnd_2819016 := by exact prefixLift 2819016
  have htrace : WordTrace (prefixWord ++ tailWord_2819016) baseStart_2819016 baseEnd_2819016 := by
    simpa [prefixWord, tailWord_2819016, baseEnd_2819016] using wordTrace_append hprefix tailTrace_2819016
  have hstable : (prefixWord ++ tailWord_2819016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2819016).length < 2 ^ (prefixWord ++ tailWord_2819016).sum := by decide
  have hdescent : baseEnd_2819016 < baseStart_2819016 := by decide
  rcases family_descends (prefixWord ++ tailWord_2819016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2819033 : List Nat := [1, 2, 1, 2, 5, 1, 3, 8]
def baseStart_2819033 : Nat := 118140960795 + 2819033 * 2 ^ 59
def prefixEnd_2819033 : Nat := 4983230072969 + 3 ^ 40 * 2819033 * 2
def baseEnd_2819033 : Nat := 53611811477265713115667

theorem tailTrace_2819033 : CollatzResearch.WordTrace tailWord_2819033 prefixEnd_2819033 53611811477265713115667 := by
  unfold tailWord_2819033
  simp only [CollatzResearch.WordTrace]
  refine ⟨102818580396132368351117753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68545720264088245567411835 102818580396132368351117753)
  ·
    refine ⟨77113935297099276263338315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102818580396132368351117753 77113935297099276263338315)
    ·
      refine ⟨115670902945648914395007473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77113935297099276263338315 115670902945648914395007473)
      ·
        refine ⟨86753177209236685796255605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115670902945648914395007473 86753177209236685796255605)
        ·
          refine ⟨8133110363365939293398963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 86753177209236685796255605 8133110363365939293398963)
          ·
            refine ⟨12199665545048908940098445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8133110363365939293398963 12199665545048908940098445)
            ·
              refine ⟨4574874579393340852536917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12199665545048908940098445 4574874579393340852536917)
              ·
                refine ⟨53611811477265713115667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4574874579393340852536917 53611811477265713115667)
                ·
                  rfl

theorem cell23_2819033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 3, 8].length) (baseStart_2819033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2819033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2819033 prefixEnd_2819033 := by exact prefixLift 2819033
  have htrace : WordTrace (prefixWord ++ tailWord_2819033) baseStart_2819033 baseEnd_2819033 := by
    simpa [prefixWord, tailWord_2819033, baseEnd_2819033] using wordTrace_append hprefix tailTrace_2819033
  have hstable : (prefixWord ++ tailWord_2819033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2819033).length < 2 ^ (prefixWord ++ tailWord_2819033).sum := by decide
  have hdescent : baseEnd_2819033 < baseStart_2819033 := by decide
  rcases family_descends (prefixWord ++ tailWord_2819033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2819037 : List Nat := [1, 4, 3, 1, 2, 1, 2, 3, 2, 4]
def baseStart_2819037 : Nat := 118140960795 + 2819037 * 2 ^ 59
def prefixEnd_2819037 : Nat := 4983230072969 + 3 ^ 40 * 2819037 * 2
def baseEnd_2819037 : Nat := 482506987936264079490997

theorem tailTrace_2819037 : CollatzResearch.WordTrace tailWord_2819037 prefixEnd_2819037 482506987936264079490997 := by
  unfold tailWord_2819037
  simp only [CollatzResearch.WordTrace]
  refine ⟨102818726288117877034263365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68545817525411918022842243 102818726288117877034263365)
  ·
    refine ⟨19278511179022101943924381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 102818726288117877034263365 19278511179022101943924381)
    ·
      refine ⟨7229441692133288228971643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19278511179022101943924381 7229441692133288228971643)
      ·
        refine ⟨10844162538199932343457465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7229441692133288228971643 10844162538199932343457465)
        ·
          refine ⟨8133121903649949257593099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10844162538199932343457465 8133121903649949257593099)
          ·
            refine ⟨12199682855474923886389649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8133121903649949257593099 12199682855474923886389649)
            ·
              refine ⟨9149762141606192914792237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12199682855474923886389649 9149762141606192914792237)
              ·
                refine ⟨3431160803102322343047089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9149762141606192914792237 3431160803102322343047089)
                ·
                  refine ⟨2573370602326741757285317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3431160803102322343047089 2573370602326741757285317)
                  ·
                    refine ⟨482506987936264079490997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2573370602326741757285317 482506987936264079490997)
                    ·
                      rfl

theorem cell23_2819037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 2, 3, 2, 4].length) (baseStart_2819037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2819037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2819037 prefixEnd_2819037 := by exact prefixLift 2819037
  have htrace : WordTrace (prefixWord ++ tailWord_2819037) baseStart_2819037 baseEnd_2819037 := by
    simpa [prefixWord, tailWord_2819037, baseEnd_2819037] using wordTrace_append hprefix tailTrace_2819037
  have hstable : (prefixWord ++ tailWord_2819037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2819037).length < 2 ^ (prefixWord ++ tailWord_2819037).sum := by decide
  have hdescent : baseEnd_2819037 < baseStart_2819037 := by decide
  rcases family_descends (prefixWord ++ tailWord_2819037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2819050 : List Nat := [3, 1, 3, 1, 2, 3, 3, 7]
def baseStart_2819050 : Nat := 118140960795 + 2819050 * 2 ^ 59
def prefixEnd_2819050 : Nat := 4983230072969 + 3 ^ 40 * 2819050 * 2
def baseEnd_2819050 : Nat := 53612134779900025467053

theorem tailTrace_2819050 : CollatzResearch.WordTrace tailWord_2819050 prefixEnd_2819050 53612134779900025467053 := by
  unfold tailWord_2819050
  simp only [CollatzResearch.WordTrace]
  refine ⟨25704800109267695063621651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68546133624713853502991069 25704800109267695063621651)
  ·
    refine ⟨38557200163901542595432477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25704800109267695063621651 38557200163901542595432477)
    ·
      refine ⟨14458950061463078473287179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38557200163901542595432477 14458950061463078473287179)
      ·
        refine ⟨21688425092194617709930769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14458950061463078473287179 21688425092194617709930769)
        ·
          refine ⟨16266318819145963282448077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21688425092194617709930769 16266318819145963282448077)
          ·
            refine ⟨6099869557179736230918029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16266318819145963282448077 6099869557179736230918029)
            ·
              refine ⟨2287451083942401086594261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6099869557179736230918029 2287451083942401086594261)
              ·
                refine ⟨53612134779900025467053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2287451083942401086594261 53612134779900025467053)
                ·
                  rfl

theorem cell23_2819050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 3, 7].length) (baseStart_2819050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2819050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2819050 prefixEnd_2819050 := by exact prefixLift 2819050
  have htrace : WordTrace (prefixWord ++ tailWord_2819050) baseStart_2819050 baseEnd_2819050 := by
    simpa [prefixWord, tailWord_2819050, baseEnd_2819050] using wordTrace_append hprefix tailTrace_2819050
  have hstable : (prefixWord ++ tailWord_2819050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2819050).length < 2 ^ (prefixWord ++ tailWord_2819050).sum := by decide
  have hdescent : baseEnd_2819050 < baseStart_2819050 := by decide
  rcases family_descends (prefixWord ++ tailWord_2819050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2819150 : List Nat := [4, 1, 1, 1, 1, 3, 2, 1, 1, 5, 3]
def baseStart_2819150 : Nat := 118140960795 + 2819150 * 2 ^ 59
def prefixEnd_2819150 : Nat := 4983230072969 + 3 ^ 40 * 2819150 * 2
def baseEnd_2819150 : Nat := 1447578987122750296359971

theorem tailTrace_2819150 : CollatzResearch.WordTrace tailWord_2819150 prefixEnd_2819150 1447578987122750296359971 := by
  unfold tailWord_2819150
  simp only [CollatzResearch.WordTrace]
  refine ⟨12852855967088562166640863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68548565157805664888751269 12852855967088562166640863)
  ·
    refine ⟨19279283950632843249961295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12852855967088562166640863 19279283950632843249961295)
    ·
      refine ⟨28918925925949264874941943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19279283950632843249961295 28918925925949264874941943)
      ·
        refine ⟨43378388888923897312412915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28918925925949264874941943 43378388888923897312412915)
        ·
          refine ⟨65067583333385845968619373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43378388888923897312412915 65067583333385845968619373)
          ·
            refine ⟨24400343750019692238232265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65067583333385845968619373 24400343750019692238232265)
            ·
              refine ⟨18300257812514769178674199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24400343750019692238232265 18300257812514769178674199)
              ·
                refine ⟨27450386718772153768011299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18300257812514769178674199 27450386718772153768011299)
                ·
                  refine ⟨41175580078158230652016949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27450386718772153768011299 41175580078158230652016949)
                  ·
                    refine ⟨3860210632327334123626589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 41175580078158230652016949 3860210632327334123626589)
                    ·
                      refine ⟨1447578987122750296359971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3860210632327334123626589 1447578987122750296359971)
                      ·
                        rfl

theorem cell23_2819150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 1, 1, 5, 3].length) (baseStart_2819150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2819150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2819150 prefixEnd_2819150 := by exact prefixLift 2819150
  have htrace : WordTrace (prefixWord ++ tailWord_2819150) baseStart_2819150 baseEnd_2819150 := by
    simpa [prefixWord, tailWord_2819150, baseEnd_2819150] using wordTrace_append hprefix tailTrace_2819150
  have hstable : (prefixWord ++ tailWord_2819150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2819150).length < 2 ^ (prefixWord ++ tailWord_2819150).sum := by decide
  have hdescent : baseEnd_2819150 < baseStart_2819150 := by decide
  rcases family_descends (prefixWord ++ tailWord_2819150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2819153 : List Nat := [1, 2, 2, 1, 3, 1, 2, 1, 3, 7]
def baseStart_2819153 : Nat := 118140960795 + 2819153 * 2 ^ 59
def prefixEnd_2819153 : Nat := 4983230072969 + 3 ^ 40 * 2819153 * 2
def baseEnd_2819153 : Nat := 482526842521571261540819

theorem tailTrace_2819153 : CollatzResearch.WordTrace tailWord_2819153 prefixEnd_2819153 482526842521571261540819 := by
  unfold tailWord_2819153
  simp only [CollatzResearch.WordTrace]
  refine ⟨102822957155697628845486113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68548638103798419230324075 102822957155697628845486113)
  ·
    refine ⟨77117217866773221634114585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102822957155697628845486113 77117217866773221634114585)
    ·
      refine ⟨57837913400079916225585939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77117217866773221634114585 57837913400079916225585939)
      ·
        refine ⟨86756870100119874338378909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57837913400079916225585939 86756870100119874338378909)
        ·
          refine ⟨32533826287544952876892091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86756870100119874338378909 32533826287544952876892091)
          ·
            refine ⟨48800739431317429315338137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32533826287544952876892091 48800739431317429315338137)
            ·
              refine ⟨36600554573488071986503603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48800739431317429315338137 36600554573488071986503603)
              ·
                refine ⟨54900831860232107979755405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36600554573488071986503603 54900831860232107979755405)
                ·
                  refine ⟨20587811947587040492408277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54900831860232107979755405 20587811947587040492408277)
                  ·
                    refine ⟨482526842521571261540819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 20587811947587040492408277 482526842521571261540819)
                    ·
                      rfl

theorem cell23_2819153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 1, 3, 7].length) (baseStart_2819153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2819153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2819153 prefixEnd_2819153 := by exact prefixLift 2819153
  have htrace : WordTrace (prefixWord ++ tailWord_2819153) baseStart_2819153 baseEnd_2819153 := by
    simpa [prefixWord, tailWord_2819153, baseEnd_2819153] using wordTrace_append hprefix tailTrace_2819153
  have hstable : (prefixWord ++ tailWord_2819153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2819153).length < 2 ^ (prefixWord ++ tailWord_2819153).sum := by decide
  have hdescent : baseEnd_2819153 < baseStart_2819153 := by decide
  rcases family_descends (prefixWord ++ tailWord_2819153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2819224 : List Nat := [2, 1, 2, 4, 2, 3, 1, 1, 2, 1, 4]
def baseStart_2819224 : Nat := 118140960795 + 2819224 * 2 ^ 59
def prefixEnd_2819224 : Nat := 4983230072969 + 3 ^ 40 * 2819224 * 2
def baseEnd_2819224 : Nat := 1447616984691183006834631

theorem tailTrace_2819224 : CollatzResearch.WordTrace tailWord_2819224 prefixEnd_2819224 1447616984691183006834631 := by
  unfold tailWord_2819224
  simp only [CollatzResearch.WordTrace]
  refine ⟨51412773369220203985660363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68550364492293605314213817 51412773369220203985660363)
  ·
    refine ⟨77119160053830305978490545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51412773369220203985660363 77119160053830305978490545)
    ·
      refine ⟨57839370040372729483867909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77119160053830305978490545 57839370040372729483867909)
      ·
        refine ⟨10844881882569886778225233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57839370040372729483867909 10844881882569886778225233)
        ·
          refine ⟨8133661411927415083668925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10844881882569886778225233 8133661411927415083668925)
          ·
            refine ⟨3050123029472780656375847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8133661411927415083668925 3050123029472780656375847)
            ·
              refine ⟨4575184544209170984563771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3050123029472780656375847 4575184544209170984563771)
              ·
                refine ⟨6862776816313756476845657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4575184544209170984563771 6862776816313756476845657)
                ·
                  refine ⟨5147082612235317357634243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6862776816313756476845657 5147082612235317357634243)
                  ·
                    refine ⟨7720623918352976036451365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5147082612235317357634243 7720623918352976036451365)
                    ·
                      refine ⟨1447616984691183006834631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7720623918352976036451365 1447616984691183006834631)
                      ·
                        rfl

theorem cell23_2819224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 1, 1, 2, 1, 4].length) (baseStart_2819224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2819224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2819224 prefixEnd_2819224 := by exact prefixLift 2819224
  have htrace : WordTrace (prefixWord ++ tailWord_2819224) baseStart_2819224 baseEnd_2819224 := by
    simpa [prefixWord, tailWord_2819224, baseEnd_2819224] using wordTrace_append hprefix tailTrace_2819224
  have hstable : (prefixWord ++ tailWord_2819224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2819224).length < 2 ^ (prefixWord ++ tailWord_2819224).sum := by decide
  have hdescent : baseEnd_2819224 < baseStart_2819224 := by decide
  rcases family_descends (prefixWord ++ tailWord_2819224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2819250 : List Nat := [3, 2, 1, 1, 1, 4, 1, 1, 1, 2, 6]
def baseStart_2819250 : Nat := 118140960795 + 2819250 * 2 ^ 59
def prefixEnd_2819250 : Nat := 4983230072969 + 3 ^ 40 * 2819250 * 2
def baseEnd_2819250 : Nat := 1447630335188199905109511

theorem tailTrace_2819250 : CollatzResearch.WordTrace tailWord_2819250 prefixEnd_2819250 1447630335188199905109511 := by
  unfold tailWord_2819250
  simp only [CollatzResearch.WordTrace]
  refine ⟨25706623759086553602941801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68550996690897476274511469 25706623759086553602941801)
  ·
    refine ⟨19279967819314915202206351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25706623759086553602941801 19279967819314915202206351)
    ·
      refine ⟨28919951728972372803309527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19279967819314915202206351 28919951728972372803309527)
      ·
        refine ⟨43379927593458559204964291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28919951728972372803309527 43379927593458559204964291)
        ·
          refine ⟨65069891390187838807446437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43379927593458559204964291 65069891390187838807446437)
          ·
            refine ⟨12200604635660219776396207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 65069891390187838807446437 12200604635660219776396207)
            ·
              refine ⟨18300906953490329664594311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12200604635660219776396207 18300906953490329664594311)
              ·
                refine ⟨27451360430235494496891467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18300906953490329664594311 27451360430235494496891467)
                ·
                  refine ⟨41177040645353241745337201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27451360430235494496891467 41177040645353241745337201)
                  ·
                    refine ⟨30882780484014931309002901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 41177040645353241745337201 30882780484014931309002901)
                    ·
                      refine ⟨1447630335188199905109511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 30882780484014931309002901 1447630335188199905109511)
                      ·
                        rfl

theorem cell23_2819250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 1, 1, 2, 6].length) (baseStart_2819250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2819250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2819250 prefixEnd_2819250 := by exact prefixLift 2819250
  have htrace : WordTrace (prefixWord ++ tailWord_2819250) baseStart_2819250 baseEnd_2819250 := by
    simpa [prefixWord, tailWord_2819250, baseEnd_2819250] using wordTrace_append hprefix tailTrace_2819250
  have hstable : (prefixWord ++ tailWord_2819250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2819250).length < 2 ^ (prefixWord ++ tailWord_2819250).sum := by decide
  have hdescent : baseEnd_2819250 < baseStart_2819250 := by decide
  rcases family_descends (prefixWord ++ tailWord_2819250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2819264 : List Nat := [2, 1, 1, 2, 6, 1, 3, 1, 6]
def baseStart_2819264 : Nat := 118140960795 + 2819264 * 2 ^ 59
def prefixEnd_2819264 : Nat := 4983230072969 + 3 ^ 40 * 2819264 * 2
def baseEnd_2819264 : Nat := 160848613768595872259383

theorem tailTrace_2819264 : CollatzResearch.WordTrace tailWord_2819264 prefixEnd_2819264 160848613768595872259383 := by
  unfold tailWord_2819264
  simp only [CollatzResearch.WordTrace]
  refine ⟨51413502829147747401388423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68551337105530329868517897 51413502829147747401388423)
  ·
    refine ⟨77120254243721621102082635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51413502829147747401388423 77120254243721621102082635)
    ·
      refine ⟨115680381365582431653123953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77120254243721621102082635 115680381365582431653123953)
      ·
        refine ⟨86760286024186823739842965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115680381365582431653123953 86760286024186823739842965)
        ·
          refine ⟨4066888407383757362805139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 86760286024186823739842965 4066888407383757362805139)
          ·
            refine ⟨6100332611075636044207709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4066888407383757362805139 6100332611075636044207709)
            ·
              refine ⟨2287624729153363516577891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6100332611075636044207709 2287624729153363516577891)
              ·
                refine ⟨3431437093730045274866837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2287624729153363516577891 3431437093730045274866837)
                ·
                  refine ⟨160848613768595872259383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3431437093730045274866837 160848613768595872259383)
                  ·
                    rfl

theorem cell23_2819264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 3, 1, 6].length) (baseStart_2819264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2819264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2819264 prefixEnd_2819264 := by exact prefixLift 2819264
  have htrace : WordTrace (prefixWord ++ tailWord_2819264) baseStart_2819264 baseEnd_2819264 := by
    simpa [prefixWord, tailWord_2819264, baseEnd_2819264] using wordTrace_append hprefix tailTrace_2819264
  have hstable : (prefixWord ++ tailWord_2819264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2819264).length < 2 ^ (prefixWord ++ tailWord_2819264).sum := by decide
  have hdescent : baseEnd_2819264 < baseStart_2819264 := by decide
  rcases family_descends (prefixWord ++ tailWord_2819264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2819267 : List Nat := [1, 1, 1, 3, 1, 1, 1, 3, 6, 3, 2]
def baseStart_2819267 : Nat := 118140960795 + 2819267 * 2 ^ 59
def prefixEnd_2819267 : Nat := 4983230072969 + 3 ^ 40 * 2819267 * 2
def baseEnd_2819267 : Nat := 1447639064359326338596933

theorem tailTrace_2819267 : CollatzResearch.WordTrace tailWord_2819267 prefixEnd_2819267 1447639064359326338596933 := by
  unfold tailWord_2819267
  simp only [CollatzResearch.WordTrace]
  refine ⟨102827115077284626315136055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68551410051523084210090703 102827115077284626315136055)
  ·
    refine ⟨154240672615926939472704083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102827115077284626315136055 154240672615926939472704083)
    ·
      refine ⟨231361008923890409209056125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154240672615926939472704083 231361008923890409209056125)
      ·
        refine ⟨86760378346458903453396047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 231361008923890409209056125 86760378346458903453396047)
        ·
          refine ⟨130140567519688355180094071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86760378346458903453396047 130140567519688355180094071)
          ·
            refine ⟨195210851279532532770141107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130140567519688355180094071 195210851279532532770141107)
            ·
              refine ⟨292816276919298799155211661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 195210851279532532770141107 292816276919298799155211661)
              ·
                refine ⟨109806103844737049683204373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 292816276919298799155211661 109806103844737049683204373)
                ·
                  refine ⟨5147161117722049203900205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 109806103844737049683204373 5147161117722049203900205)
                  ·
                    refine ⟨1930185419145768451462577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5147161117722049203900205 1930185419145768451462577)
                    ·
                      refine ⟨1447639064359326338596933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1930185419145768451462577 1447639064359326338596933)
                      ·
                        rfl

theorem cell23_2819267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 3, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 3, 6, 3, 2].length) (baseStart_2819267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2819267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2819267 prefixEnd_2819267 := by exact prefixLift 2819267
  have htrace : WordTrace (prefixWord ++ tailWord_2819267) baseStart_2819267 baseEnd_2819267 := by
    simpa [prefixWord, tailWord_2819267, baseEnd_2819267] using wordTrace_append hprefix tailTrace_2819267
  have hstable : (prefixWord ++ tailWord_2819267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2819267).length < 2 ^ (prefixWord ++ tailWord_2819267).sum := by decide
  have hdescent : baseEnd_2819267 < baseStart_2819267 := by decide
  rcases family_descends (prefixWord ++ tailWord_2819267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2819274 : List Nat := [3, 1, 2, 1, 3, 2, 2, 2, 3, 1, 3]
def baseStart_2819274 : Nat := 118140960795 + 2819274 * 2 ^ 59
def prefixEnd_2819274 : Nat := 4983230072969 + 3 ^ 40 * 2819274 * 2
def baseEnd_2819274 : Nat := 1447642658723907811209401

theorem tailTrace_2819274 : CollatzResearch.WordTrace tailWord_2819274 prefixEnd_2819274 1447642658723907811209401 := by
  unfold tailWord_2819274
  simp only [CollatzResearch.WordTrace]
  refine ⟨25706842597064816627660219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68551580258839511007093917 25706842597064816627660219)
  ·
    refine ⟨38560263895597224941490329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25706842597064816627660219 38560263895597224941490329)
    ·
      refine ⟨28920197921697918706117747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38560263895597224941490329 28920197921697918706117747)
      ·
        refine ⟨43380296882546878059176621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28920197921697918706117747 43380296882546878059176621)
        ·
          refine ⟨16267611330955079272191233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43380296882546878059176621 16267611330955079272191233)
          ·
            refine ⟨12200708498216309454143425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16267611330955079272191233 12200708498216309454143425)
            ·
              refine ⟨9150531373662232090607569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12200708498216309454143425 9150531373662232090607569)
              ·
                refine ⟨6862898530246674067955677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9150531373662232090607569 6862898530246674067955677)
                ·
                  refine ⟨2573586948842502775483379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6862898530246674067955677 2573586948842502775483379)
                  ·
                    refine ⟨3860380423263754163225069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2573586948842502775483379 3860380423263754163225069)
                    ·
                      refine ⟨1447642658723907811209401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3860380423263754163225069 1447642658723907811209401)
                      ·
                        rfl

theorem cell23_2819274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 2, 2, 3, 1, 3].length) (baseStart_2819274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2819274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2819274 prefixEnd_2819274 := by exact prefixLift 2819274
  have htrace : WordTrace (prefixWord ++ tailWord_2819274) baseStart_2819274 baseEnd_2819274 := by
    simpa [prefixWord, tailWord_2819274, baseEnd_2819274] using wordTrace_append hprefix tailTrace_2819274
  have hstable : (prefixWord ++ tailWord_2819274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2819274).length < 2 ^ (prefixWord ++ tailWord_2819274).sum := by decide
  have hdescent : baseEnd_2819274 < baseStart_2819274 := by decide
  rcases family_descends (prefixWord ++ tailWord_2819274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2819290 : List Nat := [3, 1, 1, 2, 2, 1, 1, 3, 3, 6]
def baseStart_2819290 : Nat := 118140960795 + 2819290 * 2 ^ 59
def prefixEnd_2819290 : Nat := 4983230072969 + 3 ^ 40 * 2819290 * 2
def baseEnd_2819290 : Nat := 482550291471459916203109

theorem tailTrace_2819290 : CollatzResearch.WordTrace tailWord_2819290 prefixEnd_2819290 482550291471459916203109 := by
  unfold tailWord_2819290
  simp only [CollatzResearch.WordTrace]
  refine ⟨25706988489050325310805831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68551969304134200828815549 25706988489050325310805831)
  ·
    refine ⟨38560482733575487966208747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25706988489050325310805831 38560482733575487966208747)
    ·
      refine ⟨57840724100363231949313121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38560482733575487966208747 57840724100363231949313121)
      ·
        refine ⟨43380543075272423961984841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57840724100363231949313121 43380543075272423961984841)
        ·
          refine ⟨32535407306454317971488631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43380543075272423961984841 32535407306454317971488631)
          ·
            refine ⟨48803110959681476957232947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32535407306454317971488631 48803110959681476957232947)
            ·
              refine ⟨73204666439522215435849421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48803110959681476957232947 73204666439522215435849421)
              ·
                refine ⟨27451749914820830788443533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 73204666439522215435849421 27451749914820830788443533)
                ·
                  refine ⟨10294406218057811545666325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27451749914820830788443533 10294406218057811545666325)
                  ·
                    refine ⟨482550291471459916203109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10294406218057811545666325 482550291471459916203109)
                    ·
                      rfl

theorem cell23_2819290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 3, 3, 6].length) (baseStart_2819290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2819290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2819290 prefixEnd_2819290 := by exact prefixLift 2819290
  have htrace : WordTrace (prefixWord ++ tailWord_2819290) baseStart_2819290 baseEnd_2819290 := by
    simpa [prefixWord, tailWord_2819290, baseEnd_2819290] using wordTrace_append hprefix tailTrace_2819290
  have hstable : (prefixWord ++ tailWord_2819290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2819290).length < 2 ^ (prefixWord ++ tailWord_2819290).sum := by decide
  have hdescent : baseEnd_2819290 < baseStart_2819290 := by decide
  rcases family_descends (prefixWord ++ tailWord_2819290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2819301 : List Nat := [1, 3, 1, 4, 3, 1, 1, 2, 2, 3, 2]
def baseStart_2819301 : Nat := 118140960795 + 2819301 * 2 ^ 59
def prefixEnd_2819301 : Nat := 4983230072969 + 3 ^ 40 * 2819301 * 2
def baseEnd_2819301 : Nat := 1447656522701579205571777

theorem tailTrace_2819301 : CollatzResearch.WordTrace tailWord_2819301 prefixEnd_2819301 1447656522701579205571777 := by
  unfold tailWord_2819301
  simp only [CollatzResearch.WordTrace]
  refine ⟨102828355159161450121873757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68552236772774300081249171 102828355159161450121873757)
  ·
    refine ⟨38560633184685543795702659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102828355159161450121873757 38560633184685543795702659)
    ·
      refine ⟨57840949777028315693553989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38560633184685543795702659 57840949777028315693553989)
      ·
        refine ⟨10845178083192809192541373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57840949777028315693553989 10845178083192809192541373)
        ·
          refine ⟨4066941781197303447203015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10845178083192809192541373 4066941781197303447203015)
          ·
            refine ⟨6100412671795955170804523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4066941781197303447203015 6100412671795955170804523)
            ·
              refine ⟨9150619007693932756206785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6100412671795955170804523 9150619007693932756206785)
              ·
                refine ⟨6862964255770449567155089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9150619007693932756206785 6862964255770449567155089)
                ·
                  refine ⟨5147223191827837175366317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6862964255770449567155089 5147223191827837175366317)
                  ·
                    refine ⟨1930208696935438940762369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5147223191827837175366317 1930208696935438940762369)
                    ·
                      refine ⟨1447656522701579205571777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1930208696935438940762369 1447656522701579205571777)
                      ·
                        rfl

theorem cell23_2819301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 1, 2, 2, 3, 2].length) (baseStart_2819301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2819301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2819301 prefixEnd_2819301 := by exact prefixLift 2819301
  have htrace : WordTrace (prefixWord ++ tailWord_2819301) baseStart_2819301 baseEnd_2819301 := by
    simpa [prefixWord, tailWord_2819301, baseEnd_2819301] using wordTrace_append hprefix tailTrace_2819301
  have hstable : (prefixWord ++ tailWord_2819301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2819301).length < 2 ^ (prefixWord ++ tailWord_2819301).sum := by decide
  have hdescent : baseEnd_2819301 < baseStart_2819301 := by decide
  rcases family_descends (prefixWord ++ tailWord_2819301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2819307 : List Nat := [1, 1, 1, 1, 2, 6, 2, 1, 4, 4]
def baseStart_2819307 : Nat := 118140960795 + 2819307 * 2 ^ 59
def prefixEnd_2819307 : Nat := 4983230072969 + 3 ^ 40 * 2819307 * 2
def baseEnd_2819307 : Nat := 482553201195168727365583

theorem tailTrace_2819307 : CollatzResearch.WordTrace tailWord_2819307 prefixEnd_2819307 482553201195168727365583 := by
  unfold tailWord_2819307
  simp only [CollatzResearch.WordTrace]
  refine ⟨102828573997139713146592175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68552382664759808764394783 102828573997139713146592175)
  ·
    refine ⟨154242860995709569719888263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102828573997139713146592175 154242860995709569719888263)
    ·
      refine ⟨231364291493564354579832395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154242860995709569719888263 231364291493564354579832395)
      ·
        refine ⟨347046437240346531869748593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 231364291493564354579832395 347046437240346531869748593)
        ·
          refine ⟨260284827930259898902311445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 347046437240346531869748593 260284827930259898902311445)
          ·
            refine ⟨12200851309230932761045849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 260284827930259898902311445 12200851309230932761045849)
            ·
              refine ⟨9150638481923199570784387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12200851309230932761045849 9150638481923199570784387)
              ·
                refine ⟨13725957722884799356176581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9150638481923199570784387 13725957722884799356176581)
                ·
                  refine ⟨2573617073040899879283109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13725957722884799356176581 2573617073040899879283109)
                  ·
                    refine ⟨482553201195168727365583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2573617073040899879283109 482553201195168727365583)
                    ·
                      rfl

theorem cell23_2819307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 2, 1, 4, 4].length) (baseStart_2819307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2819307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2819307 prefixEnd_2819307 := by exact prefixLift 2819307
  have htrace : WordTrace (prefixWord ++ tailWord_2819307) baseStart_2819307 baseEnd_2819307 := by
    simpa [prefixWord, tailWord_2819307, baseEnd_2819307] using wordTrace_append hprefix tailTrace_2819307
  have hstable : (prefixWord ++ tailWord_2819307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2819307).length < 2 ^ (prefixWord ++ tailWord_2819307).sum := by decide
  have hdescent : baseEnd_2819307 < baseStart_2819307 := by decide
  rcases family_descends (prefixWord ++ tailWord_2819307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2819308 : List Nat := [2, 2, 1, 1, 2, 5, 3, 2, 1, 1, 3]
def baseStart_2819308 : Nat := 118140960795 + 2819308 * 2 ^ 59
def prefixEnd_2819308 : Nat := 4983230072969 + 3 ^ 40 * 2819308 * 2
def baseEnd_2819308 : Nat := 1447660117066160678184245

theorem tailTrace_2819308 : CollatzResearch.WordTrace tailWord_2819308 prefixEnd_2819308 1447660117066160678184245 := by
  unfold tailWord_2819308
  simp only [CollatzResearch.WordTrace]
  refine ⟨51414305235068045158689289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68552406980090726878252385 51414305235068045158689289)
  ·
    refine ⟨38560728926301033869016967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51414305235068045158689289 38560728926301033869016967)
    ·
      refine ⟨57841093389451550803525451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38560728926301033869016967 57841093389451550803525451)
      ·
        refine ⟨86761640084177326205288177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57841093389451550803525451 86761640084177326205288177)
        ·
          refine ⟨65071230063132994653966133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86761640084177326205288177 65071230063132994653966133)
          ·
            refine ⟨6100427818418718248809325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 65071230063132994653966133 6100427818418718248809325)
            ·
              refine ⟨2287660431907019343303497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6100427818418718248809325 2287660431907019343303497)
              ·
                refine ⟨1715745323930264507477623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2287660431907019343303497 1715745323930264507477623)
                ·
                  refine ⟨2573617985895396761216435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1715745323930264507477623 2573617985895396761216435)
                  ·
                    refine ⟨3860426978843095141824653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2573617985895396761216435 3860426978843095141824653)
                    ·
                      refine ⟨1447660117066160678184245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3860426978843095141824653 1447660117066160678184245)
                      ·
                        rfl

theorem cell23_2819308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 3, 2, 1, 1, 3].length) (baseStart_2819308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2819308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2819308 prefixEnd_2819308 := by exact prefixLift 2819308
  have htrace : WordTrace (prefixWord ++ tailWord_2819308) baseStart_2819308 baseEnd_2819308 := by
    simpa [prefixWord, tailWord_2819308, baseEnd_2819308] using wordTrace_append hprefix tailTrace_2819308
  have hstable : (prefixWord ++ tailWord_2819308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2819308).length < 2 ^ (prefixWord ++ tailWord_2819308).sum := by decide
  have hdescent : baseEnd_2819308 < baseStart_2819308 := by decide
  rcases family_descends (prefixWord ++ tailWord_2819308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2819351 : List Nat := [1, 1, 3, 4, 1, 1, 5, 1, 1, 2, 3]
def baseStart_2819351 : Nat := 118140960795 + 2819351 * 2 ^ 59
def prefixEnd_2819351 : Nat := 4983230072969 + 3 ^ 40 * 2819351 * 2
def baseEnd_2819351 : Nat := 1447682196734304009946547

theorem tailTrace_2819351 : CollatzResearch.WordTrace tailWord_2819351 prefixEnd_2819351 1447682196734304009946547 := by
  unfold tailWord_2819351
  simp only [CollatzResearch.WordTrace]
  refine ⟨102830178808980308661193907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68553452539320205774129271 102830178808980308661193907)
  ·
    refine ⟨154245268213470462991790861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102830178808980308661193907 154245268213470462991790861)
    ·
      refine ⟨57841975580051423621921573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 154245268213470462991790861 57841975580051423621921573)
      ·
        refine ⟨10845370421259641929110295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57841975580051423621921573 10845370421259641929110295)
        ·
          refine ⟨16268055631889462893665443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10845370421259641929110295 16268055631889462893665443)
          ·
            refine ⟨24402083447834194340498165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16268055631889462893665443 24402083447834194340498165)
            ·
              refine ⟨2287695323234455719421703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24402083447834194340498165 2287695323234455719421703)
              ·
                refine ⟨3431542984851683579132555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2287695323234455719421703 3431542984851683579132555)
                ·
                  refine ⟨5147314477277525368698833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3431542984851683579132555 5147314477277525368698833)
                  ·
                    refine ⟨3860485857958144026524125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5147314477277525368698833 3860485857958144026524125)
                    ·
                      refine ⟨1447682196734304009946547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3860485857958144026524125 1447682196734304009946547)
                      ·
                        rfl

theorem cell23_2819351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 5, 1, 1, 2, 3].length) (baseStart_2819351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2819351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2819351 prefixEnd_2819351 := by exact prefixLift 2819351
  have htrace : WordTrace (prefixWord ++ tailWord_2819351) baseStart_2819351 baseEnd_2819351 := by
    simpa [prefixWord, tailWord_2819351, baseEnd_2819351] using wordTrace_append hprefix tailTrace_2819351
  have hstable : (prefixWord ++ tailWord_2819351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2819351).length < 2 ^ (prefixWord ++ tailWord_2819351).sum := by decide
  have hdescent : baseEnd_2819351 < baseStart_2819351 := by decide
  rcases family_descends (prefixWord ++ tailWord_2819351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2819365 : List Nat := [1, 3, 1, 2, 4, 1, 4, 2, 1, 2, 2]
def baseStart_2819365 : Nat := 118140960795 + 2819365 * 2 ^ 59
def prefixEnd_2819365 : Nat := 4983230072969 + 3 ^ 40 * 2819365 * 2
def baseEnd_2819365 : Nat := 1447689385463466955171483

theorem tailTrace_2819365 : CollatzResearch.WordTrace tailWord_2819365 prefixEnd_2819365 1447689385463466955171483 := by
  unfold tailWord_2819365
  simp only [CollatzResearch.WordTrace]
  refine ⟨102830689430929589052203549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68553792953953059368135699 102830689430929589052203549)
  ·
    refine ⟨38561508536598595894576331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102830689430929589052203549 38561508536598595894576331)
    ·
      refine ⟨57842262804897893841864497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38561508536598595894576331 57842262804897893841864497)
      ·
        refine ⟨43381697103673420381398373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57842262804897893841864497 43381697103673420381398373)
        ·
          refine ⟨8134068206938766321512195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43381697103673420381398373 8134068206938766321512195)
          ·
            refine ⟨12201102310408149482268293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8134068206938766321512195 12201102310408149482268293)
            ·
              refine ⟨2287706683201528027925305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12201102310408149482268293 2287706683201528027925305)
              ·
                refine ⟨1715780012401146020943979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2287706683201528027925305 1715780012401146020943979)
                ·
                  refine ⟨2573670018601719031415969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1715780012401146020943979 2573670018601719031415969)
                  ·
                    refine ⟨1930252513951289273561977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2573670018601719031415969 1930252513951289273561977)
                    ·
                      refine ⟨1447689385463466955171483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1930252513951289273561977 1447689385463466955171483)
                      ·
                        rfl

theorem cell23_2819365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 4, 2, 1, 2, 2].length) (baseStart_2819365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2819365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2819365 prefixEnd_2819365 := by exact prefixLift 2819365
  have htrace : WordTrace (prefixWord ++ tailWord_2819365) baseStart_2819365 baseEnd_2819365 := by
    simpa [prefixWord, tailWord_2819365, baseEnd_2819365] using wordTrace_append hprefix tailTrace_2819365
  have hstable : (prefixWord ++ tailWord_2819365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2819365).length < 2 ^ (prefixWord ++ tailWord_2819365).sum := by decide
  have hdescent : baseEnd_2819365 < baseStart_2819365 := by decide
  rcases family_descends (prefixWord ++ tailWord_2819365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2819381 : List Nat := [1, 3, 3, 1, 2, 2, 2, 3, 2, 1, 3]
def baseStart_2819381 : Nat := 118140960795 + 2819381 * 2 ^ 59
def prefixEnd_2819381 : Nat := 4983230072969 + 3 ^ 40 * 2819381 * 2
def baseEnd_2819381 : Nat := 1447697601153938892571409

theorem tailTrace_2819381 : CollatzResearch.WordTrace tailWord_2819381 prefixEnd_2819381 1447697601153938892571409 := by
  unfold tailWord_2819381
  simp only [CollatzResearch.WordTrace]
  refine ⟨102831272998871623784785997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68554181999247749189857331 102831272998871623784785997)
  ·
    refine ⟨38561727374576858919294749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102831272998871623784785997 38561727374576858919294749)
    ·
      refine ⟨14460647765466322094735531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38561727374576858919294749 14460647765466322094735531)
      ·
        refine ⟨21690971648199483142103297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14460647765466322094735531 21690971648199483142103297)
        ·
          refine ⟨16268228736149612356577473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21690971648199483142103297 16268228736149612356577473)
          ·
            refine ⟨12201171552112209267433105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16268228736149612356577473 12201171552112209267433105)
            ·
              refine ⟨9150878664084156950574829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12201171552112209267433105 9150878664084156950574829)
              ·
                refine ⟨3431579499031558856465561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9150878664084156950574829 3431579499031558856465561)
                ·
                  refine ⟨2573684624273669142349171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3431579499031558856465561 2573684624273669142349171)
                  ·
                    refine ⟨3860526936410503713523757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2573684624273669142349171 3860526936410503713523757)
                    ·
                      refine ⟨1447697601153938892571409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3860526936410503713523757 1447697601153938892571409)
                      ·
                        rfl

theorem cell23_2819381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 2, 3, 2, 1, 3].length) (baseStart_2819381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2819381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2819381 prefixEnd_2819381 := by exact prefixLift 2819381
  have htrace : WordTrace (prefixWord ++ tailWord_2819381) baseStart_2819381 baseEnd_2819381 := by
    simpa [prefixWord, tailWord_2819381, baseEnd_2819381] using wordTrace_append hprefix tailTrace_2819381
  have hstable : (prefixWord ++ tailWord_2819381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2819381).length < 2 ^ (prefixWord ++ tailWord_2819381).sum := by decide
  have hdescent : baseEnd_2819381 < baseStart_2819381 := by decide
  rcases family_descends (prefixWord ++ tailWord_2819381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2819417 : List Nat := [1, 2, 1, 2, 2, 2, 3, 2, 2, 2, 4]
def baseStart_2819417 : Nat := 118140960795 + 2819417 * 2 ^ 59
def prefixEnd_2819417 : Nat := 4983230072969 + 3 ^ 40 * 2819417 * 2
def baseEnd_2819417 : Nat := 1447716086457500751721243

theorem tailTrace_2819417 : CollatzResearch.WordTrace tailWord_2819417 prefixEnd_2819417 1447716086457500751721243 := by
  unfold tailWord_2819417
  simp only [CollatzResearch.WordTrace]
  refine ⟨102832586026741201933096505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68555057351160801288731003 102832586026741201933096505)
  ·
    refine ⟨77124439520055901449822379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102832586026741201933096505 77124439520055901449822379)
    ·
      refine ⟨115686659280083852174733569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77124439520055901449822379 115686659280083852174733569)
      ·
        refine ⟨86764994460062889131050177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115686659280083852174733569 86764994460062889131050177)
        ·
          refine ⟨65073745845047166848287633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86764994460062889131050177 65073745845047166848287633)
          ·
            refine ⟨48805309383785375136215725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65073745845047166848287633 48805309383785375136215725)
            ·
              refine ⟨18301991018919515676080897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48805309383785375136215725 18301991018919515676080897)
              ·
                refine ⟨13726493264189636757060673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18301991018919515676080897 13726493264189636757060673)
                ·
                  refine ⟨10294869948142227567795505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13726493264189636757060673 10294869948142227567795505)
                  ·
                    refine ⟨7721152461106670675846629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10294869948142227567795505 7721152461106670675846629)
                    ·
                      refine ⟨1447716086457500751721243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7721152461106670675846629 1447716086457500751721243)
                      ·
                        rfl

theorem cell23_2819417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 2, 2, 2, 4].length) (baseStart_2819417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2819417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2819417 prefixEnd_2819417 := by exact prefixLift 2819417
  have htrace : WordTrace (prefixWord ++ tailWord_2819417) baseStart_2819417 baseEnd_2819417 := by
    simpa [prefixWord, tailWord_2819417, baseEnd_2819417] using wordTrace_append hprefix tailTrace_2819417
  have hstable : (prefixWord ++ tailWord_2819417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2819417).length < 2 ^ (prefixWord ++ tailWord_2819417).sum := by decide
  have hdescent : baseEnd_2819417 < baseStart_2819417 := by decide
  rcases family_descends (prefixWord ++ tailWord_2819417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2819427 : List Nat := [1, 1, 1, 5, 2, 2, 1, 3, 7]
def baseStart_2819427 : Nat := 118140960795 + 2819427 * 2 ^ 59
def prefixEnd_2819427 : Nat := 4983230072969 + 3 ^ 40 * 2819427 * 2
def baseEnd_2819427 : Nat := 160857913473782856955133

theorem tailTrace_2819427 : CollatzResearch.WordTrace tailWord_2819427 prefixEnd_2819427 160857913473782856955133 := by
  unfold tailWord_2819427
  simp only [CollatzResearch.WordTrace]
  refine ⟨102832950756704973640960535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68555300504469982427307023 102832950756704973640960535)
  ·
    refine ⟨154249426135057460461440803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102832950756704973640960535 154249426135057460461440803)
    ·
      refine ⟨231374139202586190692161205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154249426135057460461440803 231374139202586190692161205)
      ·
        refine ⟨21691325550242455377390113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 231374139202586190692161205 21691325550242455377390113)
        ·
          refine ⟨16268494162681841533042585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21691325550242455377390113 16268494162681841533042585)
          ·
            refine ⟨12201370622011381149781939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16268494162681841533042585 12201370622011381149781939)
            ·
              refine ⟨18302055933017071724672909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12201370622011381149781939 18302055933017071724672909)
              ·
                refine ⟨6863270974881401896752341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18302055933017071724672909 6863270974881401896752341)
                ·
                  refine ⟨160857913473782856955133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6863270974881401896752341 160857913473782856955133)
                  ·
                    rfl

theorem cell23_2819427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 3, 7].length) (baseStart_2819427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2819427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2819427 prefixEnd_2819427 := by exact prefixLift 2819427
  have htrace : WordTrace (prefixWord ++ tailWord_2819427) baseStart_2819427 baseEnd_2819427 := by
    simpa [prefixWord, tailWord_2819427, baseEnd_2819427] using wordTrace_append hprefix tailTrace_2819427
  have hstable : (prefixWord ++ tailWord_2819427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2819427).length < 2 ^ (prefixWord ++ tailWord_2819427).sum := by decide
  have hdescent : baseEnd_2819427 < baseStart_2819427 := by decide
  rcases family_descends (prefixWord ++ tailWord_2819427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2819467 : List Nat := [1, 1, 1, 1, 4, 3, 2, 2, 1, 2, 5]
def baseStart_2819467 : Nat := 118140960795 + 2819467 * 2 ^ 59
def prefixEnd_2819467 : Nat := 4983230072969 + 3 ^ 40 * 2819467 * 2
def baseEnd_2819467 : Nat := 1447741760490225556096013

theorem tailTrace_2819467 : CollatzResearch.WordTrace tailWord_2819467 prefixEnd_2819467 1447741760490225556096013 := by
  unfold tailWord_2819467
  simp only [CollatzResearch.WordTrace]
  refine ⟨102834409676560060472416655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68556273117706706981611103 102834409676560060472416655)
  ·
    refine ⟨154251614514840090708624983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102834409676560060472416655 154251614514840090708624983)
    ·
      refine ⟨231377421772260136062937475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154251614514840090708624983 231377421772260136062937475)
      ·
        refine ⟨347066132658390204094406213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 231377421772260136062937475 347066132658390204094406213)
        ·
          refine ⟨65074899873448163267701165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 347066132658390204094406213 65074899873448163267701165)
          ·
            refine ⟨24403087452543061225387937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65074899873448163267701165 24403087452543061225387937)
            ·
              refine ⟨18302315589407295919040953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24403087452543061225387937 18302315589407295919040953)
              ·
                refine ⟨13726736692055471939280715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18302315589407295919040953 13726736692055471939280715)
                ·
                  refine ⟨20590105038083207908921073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13726736692055471939280715 20590105038083207908921073)
                  ·
                    refine ⟨15442578778562405931690805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20590105038083207908921073 15442578778562405931690805)
                    ·
                      refine ⟨1447741760490225556096013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15442578778562405931690805 1447741760490225556096013)
                      ·
                        rfl

theorem cell23_2819467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 2, 1, 2, 5].length) (baseStart_2819467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2819467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2819467 prefixEnd_2819467 := by exact prefixLift 2819467
  have htrace : WordTrace (prefixWord ++ tailWord_2819467) baseStart_2819467 baseEnd_2819467 := by
    simpa [prefixWord, tailWord_2819467, baseEnd_2819467] using wordTrace_append hprefix tailTrace_2819467
  have hstable : (prefixWord ++ tailWord_2819467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2819467).length < 2 ^ (prefixWord ++ tailWord_2819467).sum := by decide
  have hdescent : baseEnd_2819467 < baseStart_2819467 := by decide
  rcases family_descends (prefixWord ++ tailWord_2819467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2819507 : List Nat := [1, 1, 1, 2, 3, 1, 1, 3, 2, 4, 4]
def baseStart_2819507 : Nat := 118140960795 + 2819507 * 2 ^ 59
def prefixEnd_2819507 : Nat := 4983230072969 + 3 ^ 40 * 2819507 * 2
def baseEnd_2819507 : Nat := 1447762299716405399595829

theorem tailTrace_2819507 : CollatzResearch.WordTrace tailWord_2819507 prefixEnd_2819507 1447762299716405399595829 := by
  unfold tailWord_2819507
  simp only [CollatzResearch.WordTrace]
  refine ⟨102835868596415147303872775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68557245730943431535915183 102835868596415147303872775)
  ·
    refine ⟨154253802894622720955809163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102835868596415147303872775 154253802894622720955809163)
    ·
      refine ⟨231380704341934081433713745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154253802894622720955809163 231380704341934081433713745)
      ·
        refine ⟨173535528256450561075285309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 231380704341934081433713745 173535528256450561075285309)
        ·
          refine ⟨65075823096168960403231991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 173535528256450561075285309 65075823096168960403231991)
          ·
            refine ⟨97613734644253440604847987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65075823096168960403231991 97613734644253440604847987)
            ·
              refine ⟨146420601966380160907271981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97613734644253440604847987 146420601966380160907271981)
              ·
                refine ⟨54907725737392560340226993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 146420601966380160907271981 54907725737392560340226993)
                ·
                  refine ⟨41180794303044420255170245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54907725737392560340226993 41180794303044420255170245)
                  ·
                    refine ⟨7721398931820828797844421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41180794303044420255170245 7721398931820828797844421)
                    ·
                      refine ⟨1447762299716405399595829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7721398931820828797844421 1447762299716405399595829)
                      ·
                        rfl

theorem cell23_2819507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 3, 2, 4, 4].length) (baseStart_2819507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2819507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2819507 prefixEnd_2819507 := by exact prefixLift 2819507
  have htrace : WordTrace (prefixWord ++ tailWord_2819507) baseStart_2819507 baseEnd_2819507 := by
    simpa [prefixWord, tailWord_2819507, baseEnd_2819507] using wordTrace_append hprefix tailTrace_2819507
  have hstable : (prefixWord ++ tailWord_2819507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2819507).length < 2 ^ (prefixWord ++ tailWord_2819507).sum := by decide
  have hdescent : baseEnd_2819507 < baseStart_2819507 := by decide
  rcases family_descends (prefixWord ++ tailWord_2819507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2819534 : List Nat := [4, 1, 1, 1, 2, 1, 3, 4, 6]
def baseStart_2819534 : Nat := 118140960795 + 2819534 * 2 ^ 59
def prefixEnd_2819534 : Nat := 4983230072969 + 3 ^ 40 * 2819534 * 2
def baseEnd_2819534 : Nat := 160864018188230754884245

theorem tailTrace_2819534 : CollatzResearch.WordTrace tailWord_2819534 prefixEnd_2819534 160864018188230754884245 := by
  unfold tailWord_2819534
  simp only [CollatzResearch.WordTrace]
  refine ⟨12854606670914666364388207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68557902244878220610070437 12854606670914666364388207)
  ·
    refine ⟨19281910006371999546582311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12854606670914666364388207 19281910006371999546582311)
    ·
      refine ⟨28922865009557999319873467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19281910006371999546582311 28922865009557999319873467)
      ·
        refine ⟨43384297514336998979810201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28922865009557999319873467 43384297514336998979810201)
        ·
          refine ⟨32538223135752749234857651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43384297514336998979810201 32538223135752749234857651)
          ·
            refine ⟨48807334703629123852286477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32538223135752749234857651 48807334703629123852286477)
            ·
              refine ⟨18302750513860921444607429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48807334703629123852286477 18302750513860921444607429)
              ·
                refine ⟨3431765721348922770863893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18302750513860921444607429 3431765721348922770863893)
                ·
                  refine ⟨160864018188230754884245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3431765721348922770863893 160864018188230754884245)
                  ·
                    rfl

theorem cell23_2819534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 4, 6].length) (baseStart_2819534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2819534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2819534 prefixEnd_2819534 := by exact prefixLift 2819534
  have htrace : WordTrace (prefixWord ++ tailWord_2819534) baseStart_2819534 baseEnd_2819534 := by
    simpa [prefixWord, tailWord_2819534, baseEnd_2819534] using wordTrace_append hprefix tailTrace_2819534
  have hstable : (prefixWord ++ tailWord_2819534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2819534).length < 2 ^ (prefixWord ++ tailWord_2819534).sum := by decide
  have hdescent : baseEnd_2819534 < baseStart_2819534 := by decide
  rcases family_descends (prefixWord ++ tailWord_2819534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2819565 : List Nat := [1, 5, 1, 3, 2, 2, 1, 1, 2, 2, 3]
def baseStart_2819565 : Nat := 118140960795 + 2819565 * 2 ^ 59
def prefixEnd_2819565 : Nat := 4983230072969 + 3 ^ 40 * 2819565 * 2
def baseEnd_2819565 : Nat := 1447792081594366172670563

theorem tailTrace_2819565 : CollatzResearch.WordTrace tailWord_2819565 prefixEnd_2819565 1447792081594366172670563 := by
  unfold tailWord_2819565
  simp only [CollatzResearch.WordTrace]
  refine ⟨102837984030205023209484149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68558656020136682139656099 102837984030205023209484149)
  ·
    refine ⟨9641061002831720925889139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 102837984030205023209484149 9641061002831720925889139)
    ·
      refine ⟨14461591504247581388833709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9641061002831720925889139 14461591504247581388833709)
      ·
        refine ⟨5423096814092843020812641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14461591504247581388833709 5423096814092843020812641)
        ·
          refine ⟨4067322610569632265609481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5423096814092843020812641 4067322610569632265609481)
          ·
            refine ⟨3050491957927224199207111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4067322610569632265609481 3050491957927224199207111)
            ·
              refine ⟨4575737936890836298810667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3050491957927224199207111 4575737936890836298810667)
              ·
                refine ⟨6863606905336254448216001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4575737936890836298810667 6863606905336254448216001)
                ·
                  refine ⟨5147705179002190836162001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6863606905336254448216001 5147705179002190836162001)
                  ·
                    refine ⟨3860778884251643127121501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5147705179002190836162001 3860778884251643127121501)
                    ·
                      refine ⟨1447792081594366172670563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3860778884251643127121501 1447792081594366172670563)
                      ·
                        rfl

theorem cell23_2819565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 1, 1, 2, 2, 3].length) (baseStart_2819565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2819565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2819565 prefixEnd_2819565 := by exact prefixLift 2819565
  have htrace : WordTrace (prefixWord ++ tailWord_2819565) baseStart_2819565 baseEnd_2819565 := by
    simpa [prefixWord, tailWord_2819565, baseEnd_2819565] using wordTrace_append hprefix tailTrace_2819565
  have hstable : (prefixWord ++ tailWord_2819565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2819565).length < 2 ^ (prefixWord ++ tailWord_2819565).sum := by decide
  have hdescent : baseEnd_2819565 < baseStart_2819565 := by decide
  rcases family_descends (prefixWord ++ tailWord_2819565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2819571 : List Nat := [1, 1, 1, 2, 2, 2, 2, 5, 2, 3, 2]
def baseStart_2819571 : Nat := 118140960795 + 2819571 * 2 ^ 59
def prefixEnd_2819571 : Nat := 4983230072969 + 3 ^ 40 * 2819571 * 2
def baseEnd_2819571 : Nat := 1447795162478293149195535

theorem tailTrace_2819571 : CollatzResearch.WordTrace tailWord_2819571 prefixEnd_2819571 1447795162478293149195535 := by
  unfold tailWord_2819571
  simp only [CollatzResearch.WordTrace]
  refine ⟨102838202868183286234202567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68558801912122190822801711 102838202868183286234202567)
  ·
    refine ⟨154257304302274929351303851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102838202868183286234202567 154257304302274929351303851)
    ·
      refine ⟨231385956453412394026955777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154257304302274929351303851 231385956453412394026955777)
      ·
        refine ⟨173539467340059295520216833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 231385956453412394026955777 173539467340059295520216833)
        ·
          refine ⟨130154600505044471640162625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 173539467340059295520216833 130154600505044471640162625)
          ·
            refine ⟨97615950378783353730121969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 130154600505044471640162625 97615950378783353730121969)
            ·
              refine ⟨73211962784087515297591477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97615950378783353730121969 73211962784087515297591477)
              ·
                refine ⟨6863621511008204559149201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 73211962784087515297591477 6863621511008204559149201)
                ·
                  refine ⟨5147716133256153419361901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6863621511008204559149201 5147716133256153419361901)
                  ·
                    refine ⟨1930393549971057532260713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5147716133256153419361901 1930393549971057532260713)
                    ·
                      refine ⟨1447795162478293149195535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1930393549971057532260713 1447795162478293149195535)
                      ·
                        rfl

theorem cell23_2819571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 5, 2, 3, 2].length) (baseStart_2819571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2819571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2819571 prefixEnd_2819571 := by exact prefixLift 2819571
  have htrace : WordTrace (prefixWord ++ tailWord_2819571) baseStart_2819571 baseEnd_2819571 := by
    simpa [prefixWord, tailWord_2819571, baseEnd_2819571] using wordTrace_append hprefix tailTrace_2819571
  have hstable : (prefixWord ++ tailWord_2819571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2819571).length < 2 ^ (prefixWord ++ tailWord_2819571).sum := by decide
  have hdescent : baseEnd_2819571 < baseStart_2819571 := by decide
  rcases family_descends (prefixWord ++ tailWord_2819571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2819581 : List Nat := [1, 4, 1, 1, 1, 5, 1, 3, 1, 5]
def baseStart_2819581 : Nat := 118140960795 + 2819581 * 2 ^ 59
def prefixEnd_2819581 : Nat := 4983230072969 + 3 ^ 40 * 2819581 * 2
def baseEnd_2819581 : Nat := 482600099094946036690163

theorem tailTrace_2819581 : CollatzResearch.WordTrace tailWord_2819581 prefixEnd_2819581 482600099094946036690163 := by
  unfold tailWord_2819581
  simp only [CollatzResearch.WordTrace]
  refine ⟨102838567598147057942066597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68559045065431371961377731 102838567598147057942066597)
  ·
    refine ⟨19282231424652573364137487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 102838567598147057942066597 19282231424652573364137487)
    ·
      refine ⟨28923347136978860046206231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19282231424652573364137487 28923347136978860046206231)
      ·
        refine ⟨43385020705468290069309347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28923347136978860046206231 43385020705468290069309347)
        ·
          refine ⟨65077531058202435103964021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43385020705468290069309347 65077531058202435103964021)
          ·
            refine ⟨6101018536706478290996627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 65077531058202435103964021 6101018536706478290996627)
            ·
              refine ⟨9151527805059717436494941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6101018536706478290996627 9151527805059717436494941)
              ·
                refine ⟨3431822926897394038685603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9151527805059717436494941 3431822926897394038685603)
                ·
                  refine ⟨5147734390346091058028405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3431822926897394038685603 5147734390346091058028405)
                  ·
                    refine ⟨482600099094946036690163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5147734390346091058028405 482600099094946036690163)
                    ·
                      rfl

theorem cell23_2819581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 1, 3, 1, 5].length) (baseStart_2819581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2819581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2819581 prefixEnd_2819581 := by exact prefixLift 2819581
  have htrace : WordTrace (prefixWord ++ tailWord_2819581) baseStart_2819581 baseEnd_2819581 := by
    simpa [prefixWord, tailWord_2819581, baseEnd_2819581] using wordTrace_append hprefix tailTrace_2819581
  have hstable : (prefixWord ++ tailWord_2819581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2819581).length < 2 ^ (prefixWord ++ tailWord_2819581).sum := by decide
  have hdescent : baseEnd_2819581 < baseStart_2819581 := by decide
  rcases family_descends (prefixWord ++ tailWord_2819581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2819702 : List Nat := [5, 1, 1, 2, 2, 2, 2, 2, 2, 1, 3]
def baseStart_2819702 : Nat := 118140960795 + 2819702 * 2 ^ 59
def prefixEnd_2819702 : Nat := 4983230072969 + 3 ^ 40 * 2819702 * 2
def baseEnd_2819702 : Nat := 1447862428444032136657433

theorem tailTrace_2819702 : CollatzResearch.WordTrace tailWord_2819702 prefixEnd_2819702 1447862428444032136657433 := by
  unfold tailWord_2819702
  simp only [CollatzResearch.WordTrace]
  refine ⟨6427686301919293475451335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 68561987220472463738147573 6427686301919293475451335)
  ·
    refine ⟨9641529452878940213177003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6427686301919293475451335 9641529452878940213177003)
    ·
      refine ⟨14462294179318410319765505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9641529452878940213177003 14462294179318410319765505)
      ·
        refine ⟨10846720634488807739824129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14462294179318410319765505 10846720634488807739824129)
        ·
          refine ⟨8135040475866605804868097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10846720634488807739824129 8135040475866605804868097)
          ·
            refine ⟨6101280356899954353651073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8135040475866605804868097 6101280356899954353651073)
            ·
              refine ⟨4575960267674965765238305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6101280356899954353651073 4575960267674965765238305)
              ·
                refine ⟨3431970200756224323928729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4575960267674965765238305 3431970200756224323928729)
                ·
                  refine ⟨2573977650567168242946547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3431970200756224323928729 2573977650567168242946547)
                  ·
                    refine ⟨3860966475850752364419821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2573977650567168242946547 3860966475850752364419821)
                    ·
                      refine ⟨1447862428444032136657433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3860966475850752364419821 1447862428444032136657433)
                      ·
                        rfl

theorem cell23_2819702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 2, 2, 2, 1, 3].length) (baseStart_2819702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2819702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2819702 prefixEnd_2819702 := by exact prefixLift 2819702
  have htrace : WordTrace (prefixWord ++ tailWord_2819702) baseStart_2819702 baseEnd_2819702 := by
    simpa [prefixWord, tailWord_2819702, baseEnd_2819702] using wordTrace_append hprefix tailTrace_2819702
  have hstable : (prefixWord ++ tailWord_2819702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2819702).length < 2 ^ (prefixWord ++ tailWord_2819702).sum := by decide
  have hdescent : baseEnd_2819702 < baseStart_2819702 := by decide
  rcases family_descends (prefixWord ++ tailWord_2819702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2819741 : List Nat := [1, 4, 2, 1, 1, 1, 1, 1, 3, 5, 3]
def baseStart_2819741 : Nat := 118140960795 + 2819741 * 2 ^ 59
def prefixEnd_2819741 : Nat := 4983230072969 + 3 ^ 40 * 2819741 * 2
def baseEnd_2819741 : Nat := 1447882454189557484069753

theorem tailTrace_2819741 : CollatzResearch.WordTrace tailWord_2819741 prefixEnd_2819741 1447882454189557484069753 := by
  unfold tailWord_2819741
  simp only [CollatzResearch.WordTrace]
  refine ⟨102844403277567405267891077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68562935518378270178594051 102844403277567405267891077)
  ·
    refine ⟨19283325614543888487729577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 102844403277567405267891077 19283325614543888487729577)
    ·
      refine ⟨14462494210907916365797183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19283325614543888487729577 14462494210907916365797183)
      ·
        refine ⟨21693741316361874548695775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14462494210907916365797183 21693741316361874548695775)
        ·
          refine ⟨32540611974542811823043663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21693741316361874548695775 32540611974542811823043663)
          ·
            refine ⟨48810917961814217734565495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32540611974542811823043663 48810917961814217734565495)
            ·
              refine ⟨73216376942721326601848243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48810917961814217734565495 73216376942721326601848243)
              ·
                refine ⟨109824565414081989902772365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73216376942721326601848243 109824565414081989902772365)
                ·
                  refine ⟨41184212030280746213539637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 109824565414081989902772365 41184212030280746213539637)
                  ·
                    refine ⟨3861019877838819957519341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 41184212030280746213539637 3861019877838819957519341)
                    ·
                      refine ⟨1447882454189557484069753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3861019877838819957519341 1447882454189557484069753)
                      ·
                        rfl

theorem cell23_2819741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 1, 3, 5, 3].length) (baseStart_2819741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2819741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2819741 prefixEnd_2819741 := by exact prefixLift 2819741
  have htrace : WordTrace (prefixWord ++ tailWord_2819741) baseStart_2819741 baseEnd_2819741 := by
    simpa [prefixWord, tailWord_2819741, baseEnd_2819741] using wordTrace_append hprefix tailTrace_2819741
  have hstable : (prefixWord ++ tailWord_2819741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2819741).length < 2 ^ (prefixWord ++ tailWord_2819741).sum := by decide
  have hdescent : baseEnd_2819741 < baseStart_2819741 := by decide
  rcases family_descends (prefixWord ++ tailWord_2819741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2819746 : List Nat := [3, 3, 1, 4, 1, 2, 2, 1, 1, 3, 2]
def baseStart_2819746 : Nat := 118140960795 + 2819746 * 2 ^ 59
def prefixEnd_2819746 : Nat := 4983230072969 + 3 ^ 40 * 2819746 * 2
def baseEnd_2819746 : Nat := 1447885021592829964507231

theorem tailTrace_2819746 : CollatzResearch.WordTrace tailWord_2819746 prefixEnd_2819746 1447885021592829964507231 := by
  unfold tailWord_2819746
  simp only [CollatzResearch.WordTrace]
  refine ⟨25711146410637322780455773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68563057095032860747882061 25711146410637322780455773)
  ·
    refine ⟨9641679903988996042670915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25711146410637322780455773 9641679903988996042670915)
    ·
      refine ⟨14462519855983494064006373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9641679903988996042670915 14462519855983494064006373)
      ·
        refine ⟨2711722472996905137001195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14462519855983494064006373 2711722472996905137001195)
        ·
          refine ⟨4067583709495357705501793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2711722472996905137001195 4067583709495357705501793)
          ·
            refine ⟨3050687782121518279126345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4067583709495357705501793 3050687782121518279126345)
            ·
              refine ⟨2288015836591138709344759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3050687782121518279126345 2288015836591138709344759)
              ·
                refine ⟨3432023754886708064017139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2288015836591138709344759 3432023754886708064017139)
                ·
                  refine ⟨5148035632330062096025709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3432023754886708064017139 5148035632330062096025709)
                  ·
                    refine ⟨1930513362123773286009641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5148035632330062096025709 1930513362123773286009641)
                    ·
                      refine ⟨1447885021592829964507231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1930513362123773286009641 1447885021592829964507231)
                      ·
                        rfl

theorem cell23_2819746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 2, 1, 1, 3, 2].length) (baseStart_2819746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2819746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2819746 prefixEnd_2819746 := by exact prefixLift 2819746
  have htrace : WordTrace (prefixWord ++ tailWord_2819746) baseStart_2819746 baseEnd_2819746 := by
    simpa [prefixWord, tailWord_2819746, baseEnd_2819746] using wordTrace_append hprefix tailTrace_2819746
  have hstable : (prefixWord ++ tailWord_2819746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2819746).length < 2 ^ (prefixWord ++ tailWord_2819746).sum := by decide
  have hdescent : baseEnd_2819746 < baseStart_2819746 := by decide
  rcases family_descends (prefixWord ++ tailWord_2819746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2819748 : List Nat := [2, 3, 1, 2, 2, 2, 1, 5, 5]
def baseStart_2819748 : Nat := 118140960795 + 2819748 * 2 ^ 59
def prefixEnd_2819748 : Nat := 4983230072969 + 3 ^ 40 * 2819748 * 2
def baseEnd_2819748 : Nat := 160876227617126550742469

theorem tailTrace_2819748 : CollatzResearch.WordTrace tailWord_2819748 prefixEnd_2819748 160876227617126550742469 := by
  unfold tailWord_2819748
  simp only [CollatzResearch.WordTrace]
  refine ⟨51422329294271022731697949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68563105725694696975597265 51422329294271022731697949)
  ·
    refine ⟨19283373485351633524386731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51422329294271022731697949 19283373485351633524386731)
    ·
      refine ⟨28925060228027450286580097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19283373485351633524386731 28925060228027450286580097)
      ·
        refine ⟨21693795171020587714935073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28925060228027450286580097 21693795171020587714935073)
        ·
          refine ⟨16270346378265440786201305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21693795171020587714935073 16270346378265440786201305)
          ·
            refine ⟨12202759783699080589650979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16270346378265440786201305 12202759783699080589650979)
            ·
              refine ⟨18304139675548620884476469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12202759783699080589650979 18304139675548620884476469)
              ·
                refine ⟨1716013094582683207919669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18304139675548620884476469 1716013094582683207919669)
                ·
                  refine ⟨160876227617126550742469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1716013094582683207919669 160876227617126550742469)
                  ·
                    rfl

theorem cell23_2819748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 5, 5].length) (baseStart_2819748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2819748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2819748 prefixEnd_2819748 := by exact prefixLift 2819748
  have htrace : WordTrace (prefixWord ++ tailWord_2819748) baseStart_2819748 baseEnd_2819748 := by
    simpa [prefixWord, tailWord_2819748, baseEnd_2819748] using wordTrace_append hprefix tailTrace_2819748
  have hstable : (prefixWord ++ tailWord_2819748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2819748).length < 2 ^ (prefixWord ++ tailWord_2819748).sum := by decide
  have hdescent : baseEnd_2819748 < baseStart_2819748 := by decide
  rcases family_descends (prefixWord ++ tailWord_2819748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2819781 : List Nat := [1, 3, 1, 1, 1, 1, 2, 4, 4, 1, 4]
def baseStart_2819781 : Nat := 118140960795 + 2819781 * 2 ^ 59
def prefixEnd_2819781 : Nat := 4983230072969 + 3 ^ 40 * 2819781 * 2
def baseEnd_2819781 : Nat := 1447902993415737327569569

theorem tailTrace_2819781 : CollatzResearch.WordTrace tailWord_2819781 prefixEnd_2819781 1447902993415737327569569 := by
  unfold tailWord_2819781
  simp only [CollatzResearch.WordTrace]
  refine ⟨102845862197422492099347197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68563908131614994732898131 102845862197422492099347197)
  ·
    refine ⟨38567198324033434537255199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102845862197422492099347197 38567198324033434537255199)
    ·
      refine ⟨57850797486050151805882799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38567198324033434537255199 57850797486050151805882799)
      ·
        refine ⟨86776196229075227708824199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57850797486050151805882799 86776196229075227708824199)
        ·
          refine ⟨130164294343612841563236299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86776196229075227708824199 130164294343612841563236299)
          ·
            refine ⟨195246441515419262344854449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130164294343612841563236299 195246441515419262344854449)
            ·
              refine ⟨146434831136564446758640837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 195246441515419262344854449 146434831136564446758640837)
              ·
                refine ⟨27456530838105833767245157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 146434831136564446758640837 27456530838105833767245157)
                ·
                  refine ⟨5148099532144843831358467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27456530838105833767245157 5148099532144843831358467)
                  ·
                    refine ⟨7722149298217265747037701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5148099532144843831358467 7722149298217265747037701)
                    ·
                      refine ⟨1447902993415737327569569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7722149298217265747037701 1447902993415737327569569)
                      ·
                        rfl

theorem cell23_2819781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 4, 4, 1, 4].length) (baseStart_2819781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2819781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2819781 prefixEnd_2819781 := by exact prefixLift 2819781
  have htrace : WordTrace (prefixWord ++ tailWord_2819781) baseStart_2819781 baseEnd_2819781 := by
    simpa [prefixWord, tailWord_2819781, baseEnd_2819781] using wordTrace_append hprefix tailTrace_2819781
  have hstable : (prefixWord ++ tailWord_2819781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2819781).length < 2 ^ (prefixWord ++ tailWord_2819781).sum := by decide
  have hdescent : baseEnd_2819781 < baseStart_2819781 := by decide
  rcases family_descends (prefixWord ++ tailWord_2819781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2819818 : List Nat := [3, 1, 3, 1, 1, 1, 3, 1, 4, 2, 3]
def baseStart_2819818 : Nat := 118140960795 + 2819818 * 2 ^ 59
def prefixEnd_2819818 : Nat := 4983230072969 + 3 ^ 40 * 2819818 * 2
def baseEnd_2819818 : Nat := 1447921992199953682806899

theorem tailTrace_2819818 : CollatzResearch.WordTrace tailWord_2819818 prefixEnd_2819818 1447921992199953682806899 := by
  unfold tailWord_2819818
  simp only [CollatzResearch.WordTrace]
  refine ⟨25711802924572111854611027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68564807798858964945629405 25711802924572111854611027)
  ·
    refine ⟨38567704386858167781916541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25711802924572111854611027 38567704386858167781916541)
    ·
      refine ⟨14462889145071812918218703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38567704386858167781916541 14462889145071812918218703)
      ·
        refine ⟨21694333717607719377328055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14462889145071812918218703 21694333717607719377328055)
        ·
          refine ⟨32541500576411579065992083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21694333717607719377328055 32541500576411579065992083)
          ·
            refine ⟨48812250864617368598988125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32541500576411579065992083 48812250864617368598988125)
            ·
              refine ⟨18304594074231513224620547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48812250864617368598988125 18304594074231513224620547)
              ·
                refine ⟨27456891111347269836930821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18304594074231513224620547 27456891111347269836930821)
                ·
                  refine ⟨5148167083377613094424529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27456891111347269836930821 5148167083377613094424529)
                  ·
                    refine ⟨3861125312533209820818397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5148167083377613094424529 3861125312533209820818397)
                    ·
                      refine ⟨1447921992199953682806899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3861125312533209820818397 1447921992199953682806899)
                      ·
                        rfl

theorem cell23_2819818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 1, 4, 2, 3].length) (baseStart_2819818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2819818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2819818 prefixEnd_2819818 := by exact prefixLift 2819818
  have htrace : WordTrace (prefixWord ++ tailWord_2819818) baseStart_2819818 baseEnd_2819818 := by
    simpa [prefixWord, tailWord_2819818, baseEnd_2819818] using wordTrace_append hprefix tailTrace_2819818
  have hstable : (prefixWord ++ tailWord_2819818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2819818).length < 2 ^ (prefixWord ++ tailWord_2819818).sum := by decide
  have hdescent : baseEnd_2819818 < baseStart_2819818 := by decide
  rcases family_descends (prefixWord ++ tailWord_2819818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2819825 : List Nat := [1, 2, 2, 2, 2, 5, 1, 1, 3, 4]
def baseStart_2819825 : Nat := 118140960795 + 2819825 * 2 ^ 59
def prefixEnd_2819825 : Nat := 4983230072969 + 3 ^ 40 * 2819825 * 2
def baseEnd_2819825 : Nat := 482641862188178385139789

theorem tailTrace_2819825 : CollatzResearch.WordTrace tailWord_2819825 prefixEnd_2819825 482641862188178385139789 := by
  unfold tailWord_2819825
  simp only [CollatzResearch.WordTrace]
  refine ⟨102847467009263087613948929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68564978006175391742632619 102847467009263087613948929)
  ·
    refine ⟨77135600256947315710461697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102847467009263087613948929 77135600256947315710461697)
    ·
      refine ⟨57851700192710486782846273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77135600256947315710461697 57851700192710486782846273)
      ·
        refine ⟨43388775144532865087134705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57851700192710486782846273 43388775144532865087134705)
        ·
          refine ⟨32541581358399648815351029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43388775144532865087134705 32541581358399648815351029)
          ·
            refine ⟨3050773252349967076439159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 32541581358399648815351029 3050773252349967076439159)
            ·
              refine ⟨4576159878524950614658739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3050773252349967076439159 4576159878524950614658739)
              ·
                refine ⟨6864239817787425921988109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4576159878524950614658739 6864239817787425921988109)
                ·
                  refine ⟨2574089931670284720745541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6864239817787425921988109 2574089931670284720745541)
                  ·
                    refine ⟨482641862188178385139789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2574089931670284720745541 482641862188178385139789)
                    ·
                      rfl

theorem cell23_2819825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 1, 1, 3, 4].length) (baseStart_2819825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2819825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2819825 prefixEnd_2819825 := by exact prefixLift 2819825
  have htrace : WordTrace (prefixWord ++ tailWord_2819825) baseStart_2819825 baseEnd_2819825 := by
    simpa [prefixWord, tailWord_2819825, baseEnd_2819825] using wordTrace_append hprefix tailTrace_2819825
  have hstable : (prefixWord ++ tailWord_2819825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2819825).length < 2 ^ (prefixWord ++ tailWord_2819825).sum := by decide
  have hdescent : baseEnd_2819825 < baseStart_2819825 := by decide
  rcases family_descends (prefixWord ++ tailWord_2819825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2819841 : List Nat := [1, 2, 4, 1, 1, 1, 2, 2, 1, 2, 6]
def baseStart_2819841 : Nat := 118140960795 + 2819841 * 2 ^ 59
def prefixEnd_2819841 : Nat := 4983230072969 + 3 ^ 40 * 2819841 * 2
def baseEnd_2819841 : Nat := 1447933802255007092819293

theorem tailTrace_2819841 : CollatzResearch.WordTrace tailWord_2819841 prefixEnd_2819841 1447933802255007092819293 := by
  unfold tailWord_2819841
  simp only [CollatzResearch.WordTrace]
  refine ⟨102848050577205122346531377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68565367051470081564354251 102848050577205122346531377)
  ·
    refine ⟨77136037932903841759898533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102848050577205122346531377 77136037932903841759898533)
    ·
      refine ⟨14463007112419470329980975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 77136037932903841759898533 14463007112419470329980975)
      ·
        refine ⟨21694510668629205494971463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14463007112419470329980975 21694510668629205494971463)
        ·
          refine ⟨32541766002943808242457195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21694510668629205494971463 32541766002943808242457195)
          ·
            refine ⟨48812649004415712363685793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32541766002943808242457195 48812649004415712363685793)
            ·
              refine ⟨36609486753311784272764345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48812649004415712363685793 36609486753311784272764345)
              ·
                refine ⟨27457115064983838204573259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36609486753311784272764345 27457115064983838204573259)
                ·
                  refine ⟨41185672597475757306859889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27457115064983838204573259 41185672597475757306859889)
                  ·
                    refine ⟨30889254448106817980144917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 41185672597475757306859889 30889254448106817980144917)
                    ·
                      refine ⟨1447933802255007092819293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 30889254448106817980144917 1447933802255007092819293)
                      ·
                        rfl

theorem cell23_2819841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 2, 1, 2, 6].length) (baseStart_2819841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2819841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2819841 prefixEnd_2819841 := by exact prefixLift 2819841
  have htrace : WordTrace (prefixWord ++ tailWord_2819841) baseStart_2819841 baseEnd_2819841 := by
    simpa [prefixWord, tailWord_2819841, baseEnd_2819841] using wordTrace_append hprefix tailTrace_2819841
  have hstable : (prefixWord ++ tailWord_2819841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2819841).length < 2 ^ (prefixWord ++ tailWord_2819841).sum := by decide
  have hdescent : baseEnd_2819841 < baseStart_2819841 := by decide
  rcases family_descends (prefixWord ++ tailWord_2819841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2819875 : List Nat := [1, 1, 1, 4, 2, 1, 4, 2, 2, 3, 2]
def baseStart_2819875 : Nat := 118140960795 + 2819875 * 2 ^ 59
def prefixEnd_2819875 : Nat := 4983230072969 + 3 ^ 40 * 2819875 * 2
def baseEnd_2819875 : Nat := 1447951260597259959794137

theorem tailTrace_2819875 : CollatzResearch.WordTrace tailWord_2819875 prefixEnd_2819875 1447951260597259959794137 := by
  unfold tailWord_2819875
  simp only [CollatzResearch.WordTrace]
  refine ⟨102849290659081946153269079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68566193772721297435512719 102849290659081946153269079)
  ·
    refine ⟨154273935988622919229903619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102849290659081946153269079 154273935988622919229903619)
    ·
      refine ⟨231410903982934378844855429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154273935988622919229903619 231410903982934378844855429)
      ·
        refine ⟨43389544496800196033410393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 231410903982934378844855429 43389544496800196033410393)
        ·
          refine ⟨32542158372600147025057795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43389544496800196033410393 32542158372600147025057795)
          ·
            refine ⟨48813237558900220537586693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32542158372600147025057795 48813237558900220537586693)
            ·
              refine ⟨9152482042293791350797505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48813237558900220537586693 9152482042293791350797505)
              ·
                refine ⟨6864361531720343513098129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9152482042293791350797505 6864361531720343513098129)
                ·
                  refine ⟨5148271148790257634823597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6864361531720343513098129 5148271148790257634823597)
                  ·
                    refine ⟨1930601680796346613058849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5148271148790257634823597 1930601680796346613058849)
                    ·
                      refine ⟨1447951260597259959794137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1930601680796346613058849 1447951260597259959794137)
                      ·
                        rfl

theorem cell23_2819875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 4, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 4, 2, 2, 3, 2].length) (baseStart_2819875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2819875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2819875 prefixEnd_2819875 := by exact prefixLift 2819875
  have htrace : WordTrace (prefixWord ++ tailWord_2819875) baseStart_2819875 baseEnd_2819875 := by
    simpa [prefixWord, tailWord_2819875, baseEnd_2819875] using wordTrace_append hprefix tailTrace_2819875
  have hstable : (prefixWord ++ tailWord_2819875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2819875).length < 2 ^ (prefixWord ++ tailWord_2819875).sum := by decide
  have hdescent : baseEnd_2819875 < baseStart_2819875 := by decide
  rcases family_descends (prefixWord ++ tailWord_2819875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2819888 : List Nat := [2, 1, 1, 1, 2, 2, 1, 1, 4, 6, 2]
def baseStart_2819888 : Nat := 118140960795 + 2819888 * 2 ^ 59
def prefixEnd_2819888 : Nat := 4983230072969 + 3 ^ 40 * 2819888 * 2
def baseEnd_2819888 : Nat := 1447957935845768408931577

theorem tailTrace_2819888 : CollatzResearch.WordTrace tailWord_2819888 prefixEnd_2819888 1447957935845768408931577 := by
  unfold tailWord_2819888
  simp only [CollatzResearch.WordTrace]
  refine ⟨51424882404017424686746159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68566509872023232915661545 51424882404017424686746159)
  ·
    refine ⟨77137323606026137030119239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51424882404017424686746159 77137323606026137030119239)
    ·
      refine ⟨115705985409039205545178859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77137323606026137030119239 115705985409039205545178859)
      ·
        refine ⟨173558978113558808317768289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115705985409039205545178859 173558978113558808317768289)
        ·
          refine ⟨130169233585169106238326217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 173558978113558808317768289 130169233585169106238326217)
          ·
            refine ⟨97626925188876829678744663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 130169233585169106238326217 97626925188876829678744663)
            ·
              refine ⟨146440387783315244518116995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97626925188876829678744663 146440387783315244518116995)
              ·
                refine ⟨219660581674972866777175493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 146440387783315244518116995 219660581674972866777175493)
                ·
                  refine ⟨41186359064057412520720405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 219660581674972866777175493 41186359064057412520720405)
                  ·
                    refine ⟨1930610581127691211908769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 41186359064057412520720405 1930610581127691211908769)
                    ·
                      refine ⟨1447957935845768408931577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1930610581127691211908769 1447957935845768408931577)
                      ·
                        rfl

theorem cell23_2819888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 4, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 4, 6, 2].length) (baseStart_2819888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2819888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2819888 prefixEnd_2819888 := by exact prefixLift 2819888
  have htrace : WordTrace (prefixWord ++ tailWord_2819888) baseStart_2819888 baseEnd_2819888 := by
    simpa [prefixWord, tailWord_2819888, baseEnd_2819888] using wordTrace_append hprefix tailTrace_2819888
  have hstable : (prefixWord ++ tailWord_2819888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2819888).length < 2 ^ (prefixWord ++ tailWord_2819888).sum := by decide
  have hdescent : baseEnd_2819888 < baseStart_2819888 := by decide
  rcases family_descends (prefixWord ++ tailWord_2819888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2819898 : List Nat := [3, 1, 1, 1, 5, 1, 1, 3, 1, 6]
def baseStart_2819898 : Nat := 118140960795 + 2819898 * 2 ^ 59
def prefixEnd_2819898 : Nat := 4983230072969 + 3 ^ 40 * 2819898 * 2
def baseEnd_2819898 : Nat := 482654356884104456602177

theorem tailTrace_2819898 : CollatzResearch.WordTrace tailWord_2819898 prefixEnd_2819898 482654356884104456602177 := by
  unfold tailWord_2819898
  simp only [CollatzResearch.WordTrace]
  refine ⟨25712532384499655270339087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68566753025332414054237565 25712532384499655270339087)
  ·
    refine ⟨38568798576749482905508631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25712532384499655270339087 38568798576749482905508631)
    ·
      refine ⟨57853197865124224358262947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38568798576749482905508631 57853197865124224358262947)
      ·
        refine ⟨86779796797686336537394421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57853197865124224358262947 86779796797686336537394421)
        ·
          refine ⟨8135605949783094050380727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 86779796797686336537394421 8135605949783094050380727)
          ·
            refine ⟨12203408924674641075571091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8135605949783094050380727 12203408924674641075571091)
            ·
              refine ⟨18305113387011961613356637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12203408924674641075571091 18305113387011961613356637)
              ·
                refine ⟨6864417520129485605008739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18305113387011961613356637 6864417520129485605008739)
                ·
                  refine ⟨10296626280194228407513109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6864417520129485605008739 10296626280194228407513109)
                  ·
                    refine ⟨482654356884104456602177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10296626280194228407513109 482654356884104456602177)
                    ·
                      rfl

theorem cell23_2819898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 3, 1, 6].length) (baseStart_2819898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2819898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2819898 prefixEnd_2819898 := by exact prefixLift 2819898
  have htrace : WordTrace (prefixWord ++ tailWord_2819898) baseStart_2819898 baseEnd_2819898 := by
    simpa [prefixWord, tailWord_2819898, baseEnd_2819898] using wordTrace_append hprefix tailTrace_2819898
  have hstable : (prefixWord ++ tailWord_2819898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2819898).length < 2 ^ (prefixWord ++ tailWord_2819898).sum := by decide
  have hdescent : baseEnd_2819898 < baseStart_2819898 := by decide
  rcases family_descends (prefixWord ++ tailWord_2819898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2819911 : List Nat := [1, 1, 4, 1, 2, 1, 2, 11]
def baseStart_2819911 : Nat := 118140960795 + 2819911 * 2 ^ 59
def prefixEnd_2819911 : Nat := 4983230072969 + 3 ^ 40 * 2819911 * 2
def baseEnd_2819911 : Nat := 53628509107437845146073

theorem tailTrace_2819911 : CollatzResearch.WordTrace tailWord_2819911 prefixEnd_2819911 53628509107437845146073 := by
  unfold tailWord_2819911
  simp only [CollatzResearch.WordTrace]
  refine ⟨102850603686951524301579587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68567069124634349534386391 102850603686951524301579587)
  ·
    refine ⟨154275905530427286452369381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102850603686951524301579587 154275905530427286452369381)
    ·
      refine ⟨28926732286955116209819259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 154275905530427286452369381 28926732286955116209819259)
      ·
        refine ⟨43390098430432674314728889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28926732286955116209819259 43390098430432674314728889)
        ·
          refine ⟨32542573822824505736046667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43390098430432674314728889 32542573822824505736046667)
          ·
            refine ⟨48813860734236758604070001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32542573822824505736046667 48813860734236758604070001)
            ·
              refine ⟨36610395550677568953052501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48813860734236758604070001 36610395550677568953052501)
              ·
                refine ⟨53628509107437845146073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 36610395550677568953052501 53628509107437845146073)
                ·
                  rfl

theorem cell23_2819911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 11].length) (baseStart_2819911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2819911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2819911 prefixEnd_2819911 := by exact prefixLift 2819911
  have htrace : WordTrace (prefixWord ++ tailWord_2819911) baseStart_2819911 baseEnd_2819911 := by
    simpa [prefixWord, tailWord_2819911, baseEnd_2819911] using wordTrace_append hprefix tailTrace_2819911
  have hstable : (prefixWord ++ tailWord_2819911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2819911).length < 2 ^ (prefixWord ++ tailWord_2819911).sum := by decide
  have hdescent : baseEnd_2819911 < baseStart_2819911 := by decide
  rcases family_descends (prefixWord ++ tailWord_2819911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2819922 : List Nat := [3, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4]
def baseStart_2819922 : Nat := 118140960795 + 2819922 * 2 ^ 59
def prefixEnd_2819922 : Nat := 4983230072969 + 3 ^ 40 * 2819922 * 2
def baseEnd_2819922 : Nat := 1447975394188021275906421

theorem tailTrace_2819922 : CollatzResearch.WordTrace tailWord_2819922 prefixEnd_2819922 1447975394188021275906421 := by
  unfold tailWord_2819922
  simp only [CollatzResearch.WordTrace]
  refine ⟨25712751222477918295057505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68567336593274448786820013 25712751222477918295057505)
  ·
    refine ⟨19284563416858438721293129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25712751222477918295057505 19284563416858438721293129)
    ·
      refine ⟨14463422562643829040969847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19284563416858438721293129 14463422562643829040969847)
      ·
        refine ⟨21695133843965743561454771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14463422562643829040969847 21695133843965743561454771)
        ·
          refine ⟨32542700765948615342182157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21695133843965743561454771 32542700765948615342182157)
          ·
            refine ⟨12203512787230730753318309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32542700765948615342182157 12203512787230730753318309)
            ·
              refine ⟨2288158647605762016247183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12203512787230730753318309 2288158647605762016247183)
              ·
                refine ⟨3432237971408643024370775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2288158647605762016247183 3432237971408643024370775)
                ·
                  refine ⟨5148356957112964536556163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3432237971408643024370775 5148356957112964536556163)
                  ·
                    refine ⟨7722535435669446804834245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5148356957112964536556163 7722535435669446804834245)
                    ·
                      refine ⟨1447975394188021275906421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7722535435669446804834245 1447975394188021275906421)
                      ·
                        rfl

theorem cell23_2819922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4].length) (baseStart_2819922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2819922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2819922 prefixEnd_2819922 := by exact prefixLift 2819922
  have htrace : WordTrace (prefixWord ++ tailWord_2819922) baseStart_2819922 baseEnd_2819922 := by
    simpa [prefixWord, tailWord_2819922, baseEnd_2819922] using wordTrace_append hprefix tailTrace_2819922
  have hstable : (prefixWord ++ tailWord_2819922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2819922).length < 2 ^ (prefixWord ++ tailWord_2819922).sum := by decide
  have hdescent : baseEnd_2819922 < baseStart_2819922 := by decide
  rcases family_descends (prefixWord ++ tailWord_2819922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2819932 : List Nat := [2, 2, 4, 2, 2, 1, 1, 1, 4, 4]
def baseStart_2819932 : Nat := 118140960795 + 2819932 * 2 ^ 59
def prefixEnd_2819932 : Nat := 4983230072969 + 3 ^ 40 * 2819932 * 2
def baseEnd_2819932 : Nat := 482660176331522078927125

theorem tailTrace_2819932 : CollatzResearch.WordTrace tailWord_2819932 prefixEnd_2819932 482660176331522078927125 := by
  unfold tailWord_2819932
  simp only [CollatzResearch.WordTrace]
  refine ⟨51425684809937722444047025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68567579746583629925396033 51425684809937722444047025)
  ·
    refine ⟨38569263607453291833035269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51425684809937722444047025 38569263607453291833035269)
    ·
      refine ⟨7231736926397492218694113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38569263607453291833035269 7231736926397492218694113)
      ·
        refine ⟨5423802694798119164020585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7231736926397492218694113 5423802694798119164020585)
        ·
          refine ⟨4067852021098589373015439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5423802694798119164020585 4067852021098589373015439)
          ·
            refine ⟨6101778031647884059523159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4067852021098589373015439 6101778031647884059523159)
            ·
              refine ⟨9152667047471826089284739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6101778031647884059523159 9152667047471826089284739)
              ·
                refine ⟨13729000571207739133927109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9152667047471826089284739 13729000571207739133927109)
                ·
                  refine ⟨2574187607101451087611333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13729000571207739133927109 2574187607101451087611333)
                  ·
                    refine ⟨482660176331522078927125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2574187607101451087611333 482660176331522078927125)
                    ·
                      rfl

theorem cell23_2819932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 1, 1, 4, 4].length) (baseStart_2819932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2819932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2819932 prefixEnd_2819932 := by exact prefixLift 2819932
  have htrace : WordTrace (prefixWord ++ tailWord_2819932) baseStart_2819932 baseEnd_2819932 := by
    simpa [prefixWord, tailWord_2819932, baseEnd_2819932] using wordTrace_append hprefix tailTrace_2819932
  have hstable : (prefixWord ++ tailWord_2819932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2819932).length < 2 ^ (prefixWord ++ tailWord_2819932).sum := by decide
  have hdescent : baseEnd_2819932 < baseStart_2819932 := by decide
  rcases family_descends (prefixWord ++ tailWord_2819932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2819939 : List Nat := [1, 1, 1, 5, 4, 1, 2, 1, 3, 2, 2]
def baseStart_2819939 : Nat := 118140960795 + 2819939 * 2 ^ 59
def prefixEnd_2819939 : Nat := 4983230072969 + 3 ^ 40 * 2819939 * 2
def baseEnd_2819939 : Nat := 1447984123359147709393843

theorem tailTrace_2819939 : CollatzResearch.WordTrace tailWord_2819939 prefixEnd_2819939 1447984123359147709393843 := by
  unfold tailWord_2819939
  simp only [CollatzResearch.WordTrace]
  refine ⟨102851624930850085083598871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68567749953900056722399247 102851624930850085083598871)
  ·
    refine ⟨154277437396275127625398307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102851624930850085083598871 154277437396275127625398307)
    ·
      refine ⟨231416156094412691438097461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154277437396275127625398307 231416156094412691438097461)
      ·
        refine ⟨21695264633851189822321637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 231416156094412691438097461 21695264633851189822321637)
        ·
          refine ⟨4067862118847098091685307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21695264633851189822321637 4067862118847098091685307)
          ·
            refine ⟨6101793178270647137527961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4067862118847098091685307 6101793178270647137527961)
            ·
              refine ⟨4576344883702985353145971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6101793178270647137527961 4576344883702985353145971)
              ·
                refine ⟨6864517325554478029718957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4576344883702985353145971 6864517325554478029718957)
                ·
                  refine ⟨2574193997082929261144609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6864517325554478029718957 2574193997082929261144609)
                  ·
                    refine ⟨1930645497812196945858457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2574193997082929261144609 1930645497812196945858457)
                    ·
                      refine ⟨1447984123359147709393843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1930645497812196945858457 1447984123359147709393843)
                      ·
                        rfl

theorem cell23_2819939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 2, 1, 3, 2, 2].length) (baseStart_2819939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2819939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2819939 prefixEnd_2819939 := by exact prefixLift 2819939
  have htrace : WordTrace (prefixWord ++ tailWord_2819939) baseStart_2819939 baseEnd_2819939 := by
    simpa [prefixWord, tailWord_2819939, baseEnd_2819939] using wordTrace_append hprefix tailTrace_2819939
  have hstable : (prefixWord ++ tailWord_2819939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2819939).length < 2 ^ (prefixWord ++ tailWord_2819939).sum := by decide
  have hdescent : baseEnd_2819939 < baseStart_2819939 := by decide
  rcases family_descends (prefixWord ++ tailWord_2819939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2819990 : List Nat := [5, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2]
def baseStart_2819990 : Nat := 118140960795 + 2819990 * 2 ^ 59
def prefixEnd_2819990 : Nat := 4983230072969 + 3 ^ 40 * 2819990 * 2
def baseEnd_2819990 : Nat := 1448010310872527009856109

theorem tailTrace_2819990 : CollatzResearch.WordTrace tailWord_2819990 prefixEnd_2819990 1448010310872527009856109 := by
  unfold tailWord_2819990
  simp only [CollatzResearch.WordTrace]
  refine ⟨6428342815854082549606589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 68568990035776880529136949 6428342815854082549606589)
  ·
    refine ⟨2410628555945280956102471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6428342815854082549606589 2410628555945280956102471)
    ·
      refine ⟨3615942833917921434153707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2410628555945280956102471 3615942833917921434153707)
      ·
        refine ⟨5423914250876882151230561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3615942833917921434153707 5423914250876882151230561)
        ·
          refine ⟨4067935688157661613422921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5423914250876882151230561 4067935688157661613422921)
          ·
            refine ⟨3050951766118246210067191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4067935688157661613422921 3050951766118246210067191)
            ·
              refine ⟨4576427649177369315100787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3050951766118246210067191 4576427649177369315100787)
              ·
                refine ⟨6864641473766053972651181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4576427649177369315100787 6864641473766053972651181)
                ·
                  refine ⟨2574240552662270239744193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6864641473766053972651181 2574240552662270239744193)
                  ·
                    refine ⟨1930680414496702679808145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2574240552662270239744193 1930680414496702679808145)
                    ·
                      refine ⟨1448010310872527009856109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1930680414496702679808145 1448010310872527009856109)
                      ·
                        rfl

theorem cell23_2819990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2].length) (baseStart_2819990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2819990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2819990 prefixEnd_2819990 := by exact prefixLift 2819990
  have htrace : WordTrace (prefixWord ++ tailWord_2819990) baseStart_2819990 baseEnd_2819990 := by
    simpa [prefixWord, tailWord_2819990, baseEnd_2819990] using wordTrace_append hprefix tailTrace_2819990
  have hstable : (prefixWord ++ tailWord_2819990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2819990).length < 2 ^ (prefixWord ++ tailWord_2819990).sum := by decide
  have hdescent : baseEnd_2819990 < baseStart_2819990 := by decide
  rcases family_descends (prefixWord ++ tailWord_2819990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2820018 : List Nat := [3, 2, 1, 1, 1, 1, 1, 6, 7]
def baseStart_2820018 : Nat := 118140960795 + 2820018 * 2 ^ 59
def prefixEnd_2820018 : Nat := 4983230072969 + 3 ^ 40 * 2820018 * 2
def baseEnd_2820018 : Nat := 160891632036761433367331

theorem tailTrace_2820018 : CollatzResearch.WordTrace tailWord_2820018 prefixEnd_2820018 160891632036761433367331 := by
  unfold tailWord_2820018
  simp only [CollatzResearch.WordTrace]
  refine ⟨25713626574390970393931177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68569670865042587717149805 25713626574390970393931177)
  ·
    refine ⟨19285219930793227795448383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25713626574390970393931177 19285219930793227795448383)
    ·
      refine ⟨28927829896189841693172575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19285219930793227795448383 28927829896189841693172575)
      ·
        refine ⟨43391744844284762539758863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28927829896189841693172575 43391744844284762539758863)
        ·
          refine ⟨65087617266427143809638295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43391744844284762539758863 65087617266427143809638295)
          ·
            refine ⟨97631425899640715714457443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65087617266427143809638295 97631425899640715714457443)
            ·
              refine ⟨146447138849461073571686165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97631425899640715714457443 146447138849461073571686165)
              ·
                refine ⟨6864709633568487823672789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 146447138849461073571686165 6864709633568487823672789)
                ·
                  refine ⟨160891632036761433367331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6864709633568487823672789 160891632036761433367331)
                  ·
                    rfl

theorem cell23_2820018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 6, 7].length) (baseStart_2820018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2820018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2820018 prefixEnd_2820018 := by exact prefixLift 2820018
  have htrace : WordTrace (prefixWord ++ tailWord_2820018) baseStart_2820018 baseEnd_2820018 := by
    simpa [prefixWord, tailWord_2820018, baseEnd_2820018] using wordTrace_append hprefix tailTrace_2820018
  have hstable : (prefixWord ++ tailWord_2820018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2820018).length < 2 ^ (prefixWord ++ tailWord_2820018).sum := by decide
  have hdescent : baseEnd_2820018 < baseStart_2820018 := by decide
  rcases family_descends (prefixWord ++ tailWord_2820018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2820052 : List Nat := [2, 4, 1, 2, 1, 1, 3, 4, 5]
def baseStart_2820052 : Nat := 118140960795 + 2820052 * 2 ^ 59
def prefixEnd_2820052 : Nat := 4983230072969 + 3 ^ 40 * 2820052 * 2
def baseEnd_2820052 : Nat := 160893571852567307475647

theorem tailTrace_2820052 : CollatzResearch.WordTrace tailWord_2820052 prefixEnd_2820052 160893571852567307475647 := by
  unfold tailWord_2820052
  simp only [CollatzResearch.WordTrace]
  refine ⟨51427873189720352691231205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68570497586293803588308273 51427873189720352691231205)
  ·
    refine ⟨9642726223072566129605851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51427873189720352691231205 9642726223072566129605851)
    ·
      refine ⟨14464089334608849194408777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9642726223072566129605851 14464089334608849194408777)
      ·
        refine ⟨10848067000956636895806583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14464089334608849194408777 10848067000956636895806583)
        ·
          refine ⟨16272100501434955343709875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10848067000956636895806583 16272100501434955343709875)
          ·
            refine ⟨24408150752152433015564813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16272100501434955343709875 24408150752152433015564813)
            ·
              refine ⟨9153056532057162380836805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24408150752152433015564813 9153056532057162380836805)
              ·
                refine ⟨1716198099760717946406901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9153056532057162380836805 1716198099760717946406901)
                ·
                  refine ⟨160893571852567307475647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1716198099760717946406901 160893571852567307475647)
                  ·
                    rfl

theorem cell23_2820052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 3, 4, 5].length) (baseStart_2820052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2820052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2820052 prefixEnd_2820052 := by exact prefixLift 2820052
  have htrace : WordTrace (prefixWord ++ tailWord_2820052) baseStart_2820052 baseEnd_2820052 := by
    simpa [prefixWord, tailWord_2820052, baseEnd_2820052] using wordTrace_append hprefix tailTrace_2820052
  have hstable : (prefixWord ++ tailWord_2820052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2820052).length < 2 ^ (prefixWord ++ tailWord_2820052).sum := by decide
  have hdescent : baseEnd_2820052 < baseStart_2820052 := by decide
  rcases family_descends (prefixWord ++ tailWord_2820052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2820055 : List Nat := [1, 1, 3, 2, 1, 1, 3, 1, 1, 7, 2]
def baseStart_2820055 : Nat := 118140960795 + 2820055 * 2 ^ 59
def prefixEnd_2820055 : Nat := 4983230072969 + 3 ^ 40 * 2820055 * 2
def baseEnd_2820055 : Nat := 1448043687115069255543309

theorem tailTrace_2820055 : CollatzResearch.WordTrace tailWord_2820055 prefixEnd_2820055 1448043687115069255543309 := by
  unfold tailWord_2820055
  simp only [CollatzResearch.WordTrace]
  refine ⟨102855855798429836894821619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68570570532286557929881079 102855855798429836894821619)
  ·
    refine ⟨154283783697644755342232429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102855855798429836894821619 154283783697644755342232429)
    ·
      refine ⟨57856418886616783253337161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 154283783697644755342232429 57856418886616783253337161)
      ·
        refine ⟨43392314164962587440002871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57856418886616783253337161 43392314164962587440002871)
        ·
          refine ⟨65088471247443881160004307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43392314164962587440002871 65088471247443881160004307)
          ·
            refine ⟨97632706871165821740006461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65088471247443881160004307 97632706871165821740006461)
            ·
              refine ⟨36612265076687183152502423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 97632706871165821740006461 36612265076687183152502423)
              ·
                refine ⟨54918397615030774728753635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36612265076687183152502423 54918397615030774728753635)
                ·
                  refine ⟨82377596422546162093130453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54918397615030774728753635 82377596422546162093130453)
                  ·
                    refine ⟨1930724916153425674057745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 82377596422546162093130453 1930724916153425674057745)
                    ·
                      refine ⟨1448043687115069255543309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1930724916153425674057745 1448043687115069255543309)
                      ·
                        rfl

theorem cell23_2820055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 1, 1, 7, 2].length) (baseStart_2820055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2820055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2820055 prefixEnd_2820055 := by exact prefixLift 2820055
  have htrace : WordTrace (prefixWord ++ tailWord_2820055) baseStart_2820055 baseEnd_2820055 := by
    simpa [prefixWord, tailWord_2820055, baseEnd_2820055] using wordTrace_append hprefix tailTrace_2820055
  have hstable : (prefixWord ++ tailWord_2820055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2820055).length < 2 ^ (prefixWord ++ tailWord_2820055).sum := by decide
  have hdescent : baseEnd_2820055 < baseStart_2820055 := by decide
  rcases family_descends (prefixWord ++ tailWord_2820055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2820146 : List Nat := [3, 2, 1, 1, 2, 5, 1, 3, 1, 4]
def baseStart_2820146 : Nat := 118140960795 + 2820146 * 2 ^ 59
def prefixEnd_2820146 : Nat := 4983230072969 + 3 ^ 40 * 2820146 * 2
def baseEnd_2820146 : Nat := 482696804618209466501797

theorem tailTrace_2820146 : CollatzResearch.WordTrace tailWord_2820146 prefixEnd_2820146 482696804618209466501797 := by
  unfold tailWord_2820146
  simp only [CollatzResearch.WordTrace]
  refine ⟨25714793710275039859096073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68572783227400106290922861 25714793710275039859096073)
  ·
    refine ⟨19286095282706279894322055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25714793710275039859096073 19286095282706279894322055)
    ·
      refine ⟨28929142924059419841483083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19286095282706279894322055 28929142924059419841483083)
      ·
        refine ⟨43393714386089129762224625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28929142924059419841483083 43393714386089129762224625)
        ·
          refine ⟨32545285789566847321668469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43393714386089129762224625 32545285789566847321668469)
          ·
            refine ⟨3051120542771891936406419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 32545285789566847321668469 3051120542771891936406419)
            ·
              refine ⟨4576680814157837904609629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3051120542771891936406419 4576680814157837904609629)
              ·
                refine ⟨1716255305309189214228611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4576680814157837904609629 1716255305309189214228611)
                ·
                  refine ⟨2574382957963783821342917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1716255305309189214228611 2574382957963783821342917)
                  ·
                    refine ⟨482696804618209466501797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2574382957963783821342917 482696804618209466501797)
                    ·
                      rfl

theorem cell23_2820146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 1, 3, 1, 4].length) (baseStart_2820146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2820146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2820146 prefixEnd_2820146 := by exact prefixLift 2820146
  have htrace : WordTrace (prefixWord ++ tailWord_2820146) baseStart_2820146 baseEnd_2820146 := by
    simpa [prefixWord, tailWord_2820146, baseEnd_2820146] using wordTrace_append hprefix tailTrace_2820146
  have hstable : (prefixWord ++ tailWord_2820146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2820146).length < 2 ^ (prefixWord ++ tailWord_2820146).sum := by decide
  have hdescent : baseEnd_2820146 < baseStart_2820146 := by decide
  rcases family_descends (prefixWord ++ tailWord_2820146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2820175 : List Nat := [1, 1, 2, 1, 1, 2, 2, 3, 5, 1, 4]
def baseStart_2820175 : Nat := 118140960795 + 2820175 * 2 ^ 59
def prefixEnd_2820175 : Nat := 4983230072969 + 3 ^ 40 * 2820175 * 2
def baseEnd_2820175 : Nat := 1448105304793608786042757

theorem tailTrace_2820175 : CollatzResearch.WordTrace tailWord_2820175 prefixEnd_2820175 1448105304793608786042757 := by
  unfold tailWord_2820175
  simp only [CollatzResearch.WordTrace]
  refine ⟨102860232557995097389189979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68573488371996731592793319 102860232557995097389189979)
  ·
    refine ⟨154290348836992646083784969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102860232557995097389189979 154290348836992646083784969)
    ·
      refine ⟨115717761627744484562838727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154290348836992646083784969 115717761627744484562838727)
      ·
        refine ⟨173576642441616726844258091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115717761627744484562838727 173576642441616726844258091)
        ·
          refine ⟨260364963662425090266387137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173576642441616726844258091 260364963662425090266387137)
          ·
            refine ⟨195273722746818817699790353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 260364963662425090266387137 195273722746818817699790353)
            ·
              refine ⟨146455292060114113274842765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 195273722746818817699790353 146455292060114113274842765)
              ·
                refine ⟨54920734522542792478066037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 146455292060114113274842765 54920734522542792478066037)
                ·
                  refine ⟨5148818861488386794818691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 54920734522542792478066037 5148818861488386794818691)
                  ·
                    refine ⟨7723228292232580192228037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5148818861488386794818691 7723228292232580192228037)
                    ·
                      refine ⟨1448105304793608786042757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7723228292232580192228037 1448105304793608786042757)
                      ·
                        rfl

theorem cell23_2820175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 3, 5, 1, 4].length) (baseStart_2820175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2820175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2820175 prefixEnd_2820175 := by exact prefixLift 2820175
  have htrace : WordTrace (prefixWord ++ tailWord_2820175) baseStart_2820175 baseEnd_2820175 := by
    simpa [prefixWord, tailWord_2820175, baseEnd_2820175] using wordTrace_append hprefix tailTrace_2820175
  have hstable : (prefixWord ++ tailWord_2820175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2820175).length < 2 ^ (prefixWord ++ tailWord_2820175).sum := by decide
  have hdescent : baseEnd_2820175 < baseStart_2820175 := by decide
  rcases family_descends (prefixWord ++ tailWord_2820175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2820185 : List Nat := [1, 2, 1, 2, 2, 1, 4, 3, 1, 6]
def baseStart_2820185 : Nat := 118140960795 + 2820185 * 2 ^ 59
def prefixEnd_2820185 : Nat := 4983230072969 + 3 ^ 40 * 2820185 * 2
def baseEnd_2820185 : Nat := 482703479866717915639237

theorem tailTrace_2820185 : CollatzResearch.WordTrace tailWord_2820185 prefixEnd_2820185 482703479866717915639237 := by
  unfold tailWord_2820185
  simp only [CollatzResearch.WordTrace]
  refine ⟨102860597287958869097054009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68573731525305912731369339 102860597287958869097054009)
  ·
    refine ⟨77145447965969151822790507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102860597287958869097054009 77145447965969151822790507)
    ·
      refine ⟨115718171948953727734185761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77145447965969151822790507 115718171948953727734185761)
      ·
        refine ⟨86788628961715295800639321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115718171948953727734185761 86788628961715295800639321)
        ·
          refine ⟨65091471721286471850479491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86788628961715295800639321 65091471721286471850479491)
          ·
            refine ⟨97637207581929707775719237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65091471721286471850479491 97637207581929707775719237)
            ·
              refine ⟨18306976421611820207947357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 97637207581929707775719237 18306976421611820207947357)
              ·
                refine ⟨6865116158104432577980259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18306976421611820207947357 6865116158104432577980259)
                ·
                  refine ⟨10297674237156648866970389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6865116158104432577980259 10297674237156648866970389)
                  ·
                    refine ⟨482703479866717915639237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10297674237156648866970389 482703479866717915639237)
                    ·
                      rfl

theorem cell23_2820185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 3, 1, 6].length) (baseStart_2820185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2820185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2820185 prefixEnd_2820185 := by exact prefixLift 2820185
  have htrace : WordTrace (prefixWord ++ tailWord_2820185) baseStart_2820185 baseEnd_2820185 := by
    simpa [prefixWord, tailWord_2820185, baseEnd_2820185] using wordTrace_append hprefix tailTrace_2820185
  have hstable : (prefixWord ++ tailWord_2820185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2820185).length < 2 ^ (prefixWord ++ tailWord_2820185).sum := by decide
  have hdescent : baseEnd_2820185 < baseStart_2820185 := by decide
  rcases family_descends (prefixWord ++ tailWord_2820185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2820189 : List Nat := [1, 4, 4, 1, 1, 2, 1, 1, 3, 5]
def baseStart_2820189 : Nat := 118140960795 + 2820189 * 2 ^ 59
def prefixEnd_2820189 : Nat := 4983230072969 + 3 ^ 40 * 2820189 * 2
def baseEnd_2820189 : Nat := 482704164507590577089231

theorem tailTrace_2820189 : CollatzResearch.WordTrace tailWord_2820189 prefixEnd_2820189 482704164507590577089231 := by
  unfold tailWord_2820189
  simp only [CollatzResearch.WordTrace]
  refine ⟨102860743179944377780199621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68573828786629585186799747 102860743179944377780199621)
  ·
    refine ⟨19286389346239570833787429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 102860743179944377780199621 19286389346239570833787429)
    ·
      refine ⟨3616198002419919531335143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19286389346239570833787429 3616198002419919531335143)
      ·
        refine ⟨5424297003629879297002715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3616198002419919531335143 5424297003629879297002715)
        ·
          refine ⟨8136445505444818945504073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5424297003629879297002715 8136445505444818945504073)
          ·
            refine ⟨6102334129083614209128055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8136445505444818945504073 6102334129083614209128055)
            ·
              refine ⟨9153501193625421313692083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6102334129083614209128055 9153501193625421313692083)
              ·
                refine ⟨13730251790438131970538125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9153501193625421313692083 13730251790438131970538125)
                ·
                  refine ⟨5148844421414299488951797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13730251790438131970538125 5148844421414299488951797)
                  ·
                    refine ⟨482704164507590577089231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5148844421414299488951797 482704164507590577089231)
                    ·
                      rfl

theorem cell23_2820189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 1, 1, 3, 5].length) (baseStart_2820189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2820189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2820189 prefixEnd_2820189 := by exact prefixLift 2820189
  have htrace : WordTrace (prefixWord ++ tailWord_2820189) baseStart_2820189 baseEnd_2820189 := by
    simpa [prefixWord, tailWord_2820189, baseEnd_2820189] using wordTrace_append hprefix tailTrace_2820189
  have hstable : (prefixWord ++ tailWord_2820189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2820189).length < 2 ^ (prefixWord ++ tailWord_2820189).sum := by decide
  have hdescent : baseEnd_2820189 < baseStart_2820189 := by decide
  rcases family_descends (prefixWord ++ tailWord_2820189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2820192 : List Nat := [2, 1, 1, 3, 2, 4, 1, 1, 3, 1, 4]
def baseStart_2820192 : Nat := 118140960795 + 2820192 * 2 ^ 59
def prefixEnd_2820192 : Nat := 4983230072969 + 3 ^ 40 * 2820192 * 2
def baseEnd_2820192 : Nat := 1448114033964735219530179

theorem tailTrace_2820192 : CollatzResearch.WordTrace tailWord_2820192 prefixEnd_2820192 1448114033964735219530179 := by
  unfold tailWord_2820192
  simp only [CollatzResearch.WordTrace]
  refine ⟨51430426299466754646279415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68573901732622339528372553 51430426299466754646279415)
  ·
    refine ⟨77145639449200131969419123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51430426299466754646279415 77145639449200131969419123)
    ·
      refine ⟨115718459173800197954128685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77145639449200131969419123 115718459173800197954128685)
      ·
        refine ⟨43394422190175074232798257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 115718459173800197954128685 43394422190175074232798257)
        ·
          refine ⟨32545816642631305674598693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43394422190175074232798257 32545816642631305674598693)
          ·
            refine ⟨6102340620493369813987255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32545816642631305674598693 6102340620493369813987255)
            ·
              refine ⟨9153510930740054720980883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6102340620493369813987255 9153510930740054720980883)
              ·
                refine ⟨13730266396110082081471325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9153510930740054720980883 13730266396110082081471325)
                ·
                  refine ⟨5148849898541280780551747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13730266396110082081471325 5148849898541280780551747)
                  ·
                    refine ⟨7723274847811921170827621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5148849898541280780551747 7723274847811921170827621)
                    ·
                      refine ⟨1448114033964735219530179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7723274847811921170827621 1448114033964735219530179)
                      ·
                        rfl

theorem cell23_2820192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 1, 1, 3, 1, 4].length) (baseStart_2820192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2820192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2820192 prefixEnd_2820192 := by exact prefixLift 2820192
  have htrace : WordTrace (prefixWord ++ tailWord_2820192) baseStart_2820192 baseEnd_2820192 := by
    simpa [prefixWord, tailWord_2820192, baseEnd_2820192] using wordTrace_append hprefix tailTrace_2820192
  have hstable : (prefixWord ++ tailWord_2820192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2820192).length < 2 ^ (prefixWord ++ tailWord_2820192).sum := by decide
  have hdescent : baseEnd_2820192 < baseStart_2820192 := by decide
  rcases family_descends (prefixWord ++ tailWord_2820192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2820195 : List Nat := [1, 1, 1, 5, 1, 1, 2, 2, 3, 1, 5]
def baseStart_2820195 : Nat := 118140960795 + 2820195 * 2 ^ 59
def prefixEnd_2820195 : Nat := 4983230072969 + 3 ^ 40 * 2820195 * 2
def baseEnd_2820195 : Nat := 1448115574406698707792665

theorem tailTrace_2820195 : CollatzResearch.WordTrace tailWord_2820195 prefixEnd_2820195 1448115574406698707792665 := by
  unfold tailWord_2820195
  simp only [CollatzResearch.WordTrace]
  refine ⟨102860962017922640804918039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68573974678615093869945359 102860962017922640804918039)
  ·
    refine ⟨154291443026883961207377059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102860962017922640804918039 154291443026883961207377059)
    ·
      refine ⟨231437164540325941811065589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154291443026883961207377059 231437164540325941811065589)
      ·
        refine ⟨21697234175655557044787399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 231437164540325941811065589 21697234175655557044787399)
        ·
          refine ⟨32545851263483335567181099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21697234175655557044787399 32545851263483335567181099)
          ·
            refine ⟨48818776895225003350771649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32545851263483335567181099 48818776895225003350771649)
            ·
              refine ⟨36614082671418752513078737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48818776895225003350771649 36614082671418752513078737)
              ·
                refine ⟨27460562003564064384809053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36614082671418752513078737 27460562003564064384809053)
                ·
                  refine ⟨10297710751336524144303395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27460562003564064384809053 10297710751336524144303395)
                  ·
                    refine ⟨15446566127004786216455093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10297710751336524144303395 15446566127004786216455093)
                    ·
                      refine ⟨1448115574406698707792665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15446566127004786216455093 1448115574406698707792665)
                      ·
                        rfl

theorem cell23_2820195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 2, 3, 1, 5].length) (baseStart_2820195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2820195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2820195 prefixEnd_2820195 := by exact prefixLift 2820195
  have htrace : WordTrace (prefixWord ++ tailWord_2820195) baseStart_2820195 baseEnd_2820195 := by
    simpa [prefixWord, tailWord_2820195, baseEnd_2820195] using wordTrace_append hprefix tailTrace_2820195
  have hstable : (prefixWord ++ tailWord_2820195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2820195).length < 2 ^ (prefixWord ++ tailWord_2820195).sum := by decide
  have hdescent : baseEnd_2820195 < baseStart_2820195 := by decide
  rcases family_descends (prefixWord ++ tailWord_2820195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2820209 : List Nat := [1, 2, 2, 2, 1, 1, 7, 1, 1, 1, 4]
def baseStart_2820209 : Nat := 118140960795 + 2820209 * 2 ^ 59
def prefixEnd_2820209 : Nat := 4983230072969 + 3 ^ 40 * 2820209 * 2
def baseEnd_2820209 : Nat := 1448122763135861653017601

theorem tailTrace_2820209 : CollatzResearch.WordTrace tailWord_2820209 prefixEnd_2820209 1448122763135861653017601 := by
  unfold tailWord_2820209
  simp only [CollatzResearch.WordTrace]
  refine ⟨102861472639871921195927681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68574315093247947463951787 102861472639871921195927681)
  ·
    refine ⟨77146104479903940896945761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102861472639871921195927681 77146104479903940896945761)
    ·
      refine ⟨57859578359927955672709321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77146104479903940896945761 57859578359927955672709321)
      ·
        refine ⟨43394683769945966754531991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57859578359927955672709321 43394683769945966754531991)
        ·
          refine ⟨65092025654918950131797987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43394683769945966754531991 65092025654918950131797987)
          ·
            refine ⟨97638038482378425197696981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65092025654918950131797987 97638038482378425197696981)
            ·
              refine ⟨2288391526930744340571023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 97638038482378425197696981 2288391526930744340571023)
              ·
                refine ⟨3432587290396116510856535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2288391526930744340571023 3432587290396116510856535)
                ·
                  refine ⟨5148880935594174766284803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3432587290396116510856535 5148880935594174766284803)
                  ·
                    refine ⟨7723321403391262149427205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5148880935594174766284803 7723321403391262149427205)
                    ·
                      refine ⟨1448122763135861653017601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7723321403391262149427205 1448122763135861653017601)
                      ·
                        rfl

theorem cell23_2820209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 7, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 7, 1, 1, 1, 4].length) (baseStart_2820209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2820209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2820209 prefixEnd_2820209 := by exact prefixLift 2820209
  have htrace : WordTrace (prefixWord ++ tailWord_2820209) baseStart_2820209 baseEnd_2820209 := by
    simpa [prefixWord, tailWord_2820209, baseEnd_2820209] using wordTrace_append hprefix tailTrace_2820209
  have hstable : (prefixWord ++ tailWord_2820209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2820209).length < 2 ^ (prefixWord ++ tailWord_2820209).sum := by decide
  have hdescent : baseEnd_2820209 < baseStart_2820209 := by decide
  rcases family_descends (prefixWord ++ tailWord_2820209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2820232 : List Nat := [2, 1, 3, 4, 1, 1, 3, 8]
def baseStart_2820232 : Nat := 118140960795 + 2820232 * 2 ^ 59
def prefixEnd_2820232 : Nat := 4983230072969 + 3 ^ 40 * 2820232 * 2
def baseEnd_2820232 : Nat := 53634613821885743075185

theorem tailTrace_2820232 : CollatzResearch.WordTrace tailWord_2820232 prefixEnd_2820232 53634613821885743075185 := by
  unfold tailWord_2820232
  simp only [CollatzResearch.WordTrace]
  refine ⟨51431155759394298062007475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68574874345859064082676633 51431155759394298062007475)
  ·
    refine ⟨77146733639091447093011213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51431155759394298062007475 77146733639091447093011213)
    ·
      refine ⟨28930025114659292659879205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77146733639091447093011213 28930025114659292659879205)
      ·
        refine ⟨5424379708998617373727351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28930025114659292659879205 5424379708998617373727351)
        ·
          refine ⟨8136569563497926060591027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5424379708998617373727351 8136569563497926060591027)
          ·
            refine ⟨12204854345246889090886541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8136569563497926060591027 12204854345246889090886541)
            ·
              refine ⟨4576820379467583409082453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12204854345246889090886541 4576820379467583409082453)
              ·
                refine ⟨53634613821885743075185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4576820379467583409082453 53634613821885743075185)
                ·
                  rfl

theorem cell23_2820232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 3, 8].length) (baseStart_2820232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2820232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2820232 prefixEnd_2820232 := by exact prefixLift 2820232
  have htrace : WordTrace (prefixWord ++ tailWord_2820232) baseStart_2820232 baseEnd_2820232 := by
    simpa [prefixWord, tailWord_2820232, baseEnd_2820232] using wordTrace_append hprefix tailTrace_2820232
  have hstable : (prefixWord ++ tailWord_2820232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2820232).length < 2 ^ (prefixWord ++ tailWord_2820232).sum := by decide
  have hdescent : baseEnd_2820232 < baseStart_2820232 := by decide
  rcases family_descends (prefixWord ++ tailWord_2820232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2820245 : List Nat := [1, 3, 2, 1, 1, 1, 3, 2, 2, 7]
def baseStart_2820245 : Nat := 118140960795 + 2820245 * 2 ^ 59
def prefixEnd_2820245 : Nat := 4983230072969 + 3 ^ 40 * 2820245 * 2
def baseEnd_2820245 : Nat := 482713749479807837389145

theorem tailTrace_2820245 : CollatzResearch.WordTrace tailWord_2820245 prefixEnd_2820245 482713749479807837389145 := by
  unfold tailWord_2820245
  simp only [CollatzResearch.WordTrace]
  refine ⟨102862785667741499344238189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68575190445160999562825459 102862785667741499344238189)
  ·
    refine ⟨38573544625403062254089321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102862785667741499344238189 38573544625403062254089321)
    ·
      refine ⟨28930158469052296690566991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38573544625403062254089321 28930158469052296690566991)
      ·
        refine ⟨43395237703578445035850487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28930158469052296690566991 43395237703578445035850487)
        ·
          refine ⟨65092856555367667553775731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43395237703578445035850487 65092856555367667553775731)
          ·
            refine ⟨97639284833051501330663597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65092856555367667553775731 97639284833051501330663597)
            ·
              refine ⟨36614731812394312998998849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 97639284833051501330663597 36614731812394312998998849)
              ·
                refine ⟨27461048859295734749249137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36614731812394312998998849 27461048859295734749249137)
                ·
                  refine ⟨20595786644471801061936853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27461048859295734749249137 20595786644471801061936853)
                  ·
                    refine ⟨482713749479807837389145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 20595786644471801061936853 482713749479807837389145)
                    ·
                      rfl

theorem cell23_2820245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 2, 2, 7].length) (baseStart_2820245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2820245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2820245 prefixEnd_2820245 := by exact prefixLift 2820245
  have htrace : WordTrace (prefixWord ++ tailWord_2820245) baseStart_2820245 baseEnd_2820245 := by
    simpa [prefixWord, tailWord_2820245, baseEnd_2820245] using wordTrace_append hprefix tailTrace_2820245
  have hstable : (prefixWord ++ tailWord_2820245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2820245).length < 2 ^ (prefixWord ++ tailWord_2820245).sum := by decide
  have hdescent : baseEnd_2820245 < baseStart_2820245 := by decide
  rcases family_descends (prefixWord ++ tailWord_2820245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2820260 : List Nat := [2, 3, 1, 2, 4, 1, 2, 3, 1, 2, 2]
def baseStart_2820260 : Nat := 118140960795 + 2820260 * 2 ^ 59
def prefixEnd_2820260 : Nat := 4983230072969 + 3 ^ 40 * 2820260 * 2
def baseEnd_2820260 : Nat := 1448148950649240953479867

theorem tailTrace_2820260 : CollatzResearch.WordTrace tailWord_2820260 prefixEnd_2820260 1448148950649240953479867 := by
  unfold tailWord_2820260
  simp only [CollatzResearch.WordTrace]
  refine ⟨51431666381343578453017117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68575555175124771270689489 51431666381343578453017117)
  ·
    refine ⟨19286874893003841919881419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51431666381343578453017117 19286874893003841919881419)
    ·
      refine ⟨28930312339505762879822129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19286874893003841919881419 28930312339505762879822129)
      ·
        refine ⟨21697734254629322159866597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28930312339505762879822129 21697734254629322159866597)
        ·
          refine ⟨4068325172742997904974987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21697734254629322159866597 4068325172742997904974987)
          ·
            refine ⟨6102487759114496857462481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4068325172742997904974987 6102487759114496857462481)
            ·
              refine ⟨4576865819335872643096861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6102487759114496857462481 4576865819335872643096861)
              ·
                refine ⟨1716324682250952241161323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4576865819335872643096861 1716324682250952241161323)
                ·
                  refine ⟨2574487023376428361741985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1716324682250952241161323 2574487023376428361741985)
                  ·
                    refine ⟨1930865267532321271306489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2574487023376428361741985 1930865267532321271306489)
                    ·
                      refine ⟨1448148950649240953479867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1930865267532321271306489 1448148950649240953479867)
                      ·
                        rfl

theorem cell23_2820260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 2, 3, 1, 2, 2].length) (baseStart_2820260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2820260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2820260 prefixEnd_2820260 := by exact prefixLift 2820260
  have htrace : WordTrace (prefixWord ++ tailWord_2820260) baseStart_2820260 baseEnd_2820260 := by
    simpa [prefixWord, tailWord_2820260, baseEnd_2820260] using wordTrace_append hprefix tailTrace_2820260
  have hstable : (prefixWord ++ tailWord_2820260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2820260).length < 2 ^ (prefixWord ++ tailWord_2820260).sum := by decide
  have hdescent : baseEnd_2820260 < baseStart_2820260 := by decide
  rcases family_descends (prefixWord ++ tailWord_2820260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2820270 : List Nat := [4, 1, 4, 2, 1, 2, 1, 2, 2, 4]
def baseStart_2820270 : Nat := 118140960795 + 2820270 * 2 ^ 59
def prefixEnd_2820270 : Nat := 4983230072969 + 3 ^ 40 * 2820270 * 2
def baseEnd_2820270 : Nat := 482718028485261971451607

theorem tailTrace_2820270 : CollatzResearch.WordTrace tailWord_2820270 prefixEnd_2820270 482718028485261971451607 := by
  unfold tailWord_2820270
  simp only [CollatzResearch.WordTrace]
  refine ⟨12857962186581366076737283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68575798328433952409265509 12857962186581366076737283)
  ·
    refine ⟨19286943279872049115105925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12857962186581366076737283 19286943279872049115105925)
    ·
      refine ⟨3616301864976009209082361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19286943279872049115105925 3616301864976009209082361)
      ·
        refine ⟨2712226398732006906811771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3616301864976009209082361 2712226398732006906811771)
        ·
          refine ⟨4068339598098010360217657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2712226398732006906811771 4068339598098010360217657)
          ·
            refine ⟨3051254698573507770163243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4068339598098010360217657 3051254698573507770163243)
            ·
              refine ⟨4576882047860261655244865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3051254698573507770163243 4576882047860261655244865)
              ·
                refine ⟨3432661535895196241433649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4576882047860261655244865 3432661535895196241433649)
                ·
                  refine ⟨2574496151921397181075237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3432661535895196241433649 2574496151921397181075237)
                  ·
                    refine ⟨482718028485261971451607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2574496151921397181075237 482718028485261971451607)
                    ·
                      rfl

theorem cell23_2820270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 1, 2, 2, 4].length) (baseStart_2820270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2820270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2820270 prefixEnd_2820270 := by exact prefixLift 2820270
  have htrace : WordTrace (prefixWord ++ tailWord_2820270) baseStart_2820270 baseEnd_2820270 := by
    simpa [prefixWord, tailWord_2820270, baseEnd_2820270] using wordTrace_append hprefix tailTrace_2820270
  have hstable : (prefixWord ++ tailWord_2820270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2820270).length < 2 ^ (prefixWord ++ tailWord_2820270).sum := by decide
  have hdescent : baseEnd_2820270 < baseStart_2820270 := by decide
  rcases family_descends (prefixWord ++ tailWord_2820270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2820315 : List Nat := [1, 1, 1, 1, 1, 1, 1, 6, 1, 2, 7]
def baseStart_2820315 : Nat := 118140960795 + 2820315 * 2 ^ 59
def prefixEnd_2820315 : Nat := 4983230072969 + 3 ^ 40 * 2820315 * 2
def baseEnd_2820315 : Nat := 1448177192085238238292113

theorem tailTrace_2820315 : CollatzResearch.WordTrace tailWord_2820315 prefixEnd_2820315 1448177192085238238292113 := by
  unfold tailWord_2820315
  simp only [CollatzResearch.WordTrace]
  refine ⟨102865338777487901299286399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68576892518325267532857599 102865338777487901299286399)
  ·
    refine ⟨154298008166231851948929599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102865338777487901299286399 154298008166231851948929599)
    ·
      refine ⟨231447012249347777923394399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154298008166231851948929599 231447012249347777923394399)
      ·
        refine ⟨347170518374021666885091599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 231447012249347777923394399 347170518374021666885091599)
        ·
          refine ⟨520755777561032500327637399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 347170518374021666885091599 520755777561032500327637399)
          ·
            refine ⟨781133666341548750491456099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 520755777561032500327637399 781133666341548750491456099)
            ·
              refine ⟨1171700499512323125737184149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 781133666341548750491456099 1171700499512323125737184149)
              ·
                refine ⟨54923460914640146518930507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1171700499512323125737184149 54923460914640146518930507)
                ·
                  refine ⟨82385191371960219778395761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54923460914640146518930507 82385191371960219778395761)
                  ·
                    refine ⟨61788893528970164833796821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 82385191371960219778395761 61788893528970164833796821)
                    ·
                      refine ⟨1448177192085238238292113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 61788893528970164833796821 1448177192085238238292113)
                      ·
                        rfl

theorem cell23_2820315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 1, 2, 7].length) (baseStart_2820315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2820315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2820315 prefixEnd_2820315 := by exact prefixLift 2820315
  have htrace : WordTrace (prefixWord ++ tailWord_2820315) baseStart_2820315 baseEnd_2820315 := by
    simpa [prefixWord, tailWord_2820315, baseEnd_2820315] using wordTrace_append hprefix tailTrace_2820315
  have hstable : (prefixWord ++ tailWord_2820315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2820315).length < 2 ^ (prefixWord ++ tailWord_2820315).sum := by decide
  have hdescent : baseEnd_2820315 < baseStart_2820315 := by decide
  rcases family_descends (prefixWord ++ tailWord_2820315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2820369 : List Nat := [1, 2, 2, 1, 1, 6, 2, 1, 2, 5]
def baseStart_2820369 : Nat := 118140960795 + 2820369 * 2 ^ 59
def prefixEnd_2820369 : Nat := 4983230072969 + 3 ^ 40 * 2820369 * 2
def baseEnd_2820369 : Nat := 482734973346860342338955

theorem tailTrace_2820369 : CollatzResearch.WordTrace tailWord_2820369 prefixEnd_2820369 482734973346860342338955 := by
  unfold tailWord_2820369
  simp only [CollatzResearch.WordTrace]
  refine ⟨102867308319292268521752161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68578205546194845681168107 102867308319292268521752161)
  ·
    refine ⟨77150481239469201391314121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102867308319292268521752161 77150481239469201391314121)
    ·
      refine ⟨57862860929601901043485591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77150481239469201391314121 57862860929601901043485591)
      ·
        refine ⟨86794291394402851565228387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57862860929601901043485591 86794291394402851565228387)
        ·
          refine ⟨130191437091604277347842581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86794291394402851565228387 130191437091604277347842581)
          ·
            refine ⟨6102723613668950500680121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 130191437091604277347842581 6102723613668950500680121)
            ·
              refine ⟨4577042710251712875510091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6102723613668950500680121 4577042710251712875510091)
              ·
                refine ⟨6865564065377569313265137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4577042710251712875510091 6865564065377569313265137)
                ·
                  refine ⟨5149173049033176984948853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6865564065377569313265137 5149173049033176984948853)
                  ·
                    refine ⟨482734973346860342338955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5149173049033176984948853 482734973346860342338955)
                    ·
                      rfl

theorem cell23_2820369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 5].length) (baseStart_2820369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2820369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2820369 prefixEnd_2820369 := by exact prefixLift 2820369
  have htrace : WordTrace (prefixWord ++ tailWord_2820369) baseStart_2820369 baseEnd_2820369 := by
    simpa [prefixWord, tailWord_2820369, baseEnd_2820369] using wordTrace_append hprefix tailTrace_2820369
  have hstable : (prefixWord ++ tailWord_2820369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2820369).length < 2 ^ (prefixWord ++ tailWord_2820369).sum := by decide
  have hdescent : baseEnd_2820369 < baseStart_2820369 := by decide
  rcases family_descends (prefixWord ++ tailWord_2820369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2820420 : List Nat := [2, 3, 4, 1, 3, 1, 1, 1, 2, 5]
def baseStart_2820420 : Nat := 118140960795 + 2820420 * 2 ^ 59
def prefixEnd_2820420 : Nat := 4983230072969 + 3 ^ 40 * 2820420 * 2
def baseEnd_2820420 : Nat := 482743702517986775826377

theorem tailTrace_2820420 : CollatzResearch.WordTrace tailWord_2820420 prefixEnd_2820420 482743702517986775826377 := by
  unfold tailWord_2820420
  simp only [CollatzResearch.WordTrace]
  refine ⟨51434584221053752115929357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68579445628071669487905809 51434584221053752115929357)
  ·
    refine ⟨19287969082895157043473509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51434584221053752115929357 19287969082895157043473509)
    ·
      refine ⟨3616494203042841945651283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19287969082895157043473509 3616494203042841945651283)
      ·
        refine ⟨5424741304564262918476925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3616494203042841945651283 5424741304564262918476925)
        ·
          refine ⟨2034277989211598594428847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5424741304564262918476925 2034277989211598594428847)
          ·
            refine ⟨3051416983817397891643271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2034277989211598594428847 3051416983817397891643271)
            ·
              refine ⟨4577125475726096837464907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3051416983817397891643271 4577125475726096837464907)
              ·
                refine ⟨6865688213589145256197361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4577125475726096837464907 6865688213589145256197361)
                ·
                  refine ⟨5149266160191858942148021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6865688213589145256197361 5149266160191858942148021)
                  ·
                    refine ⟨482743702517986775826377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5149266160191858942148021 482743702517986775826377)
                    ·
                      rfl

theorem cell23_2820420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 1, 1, 2, 5].length) (baseStart_2820420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2820420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2820420 prefixEnd_2820420 := by exact prefixLift 2820420
  have htrace : WordTrace (prefixWord ++ tailWord_2820420) baseStart_2820420 baseEnd_2820420 := by
    simpa [prefixWord, tailWord_2820420, baseEnd_2820420] using wordTrace_append hprefix tailTrace_2820420
  have hstable : (prefixWord ++ tailWord_2820420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2820420).length < 2 ^ (prefixWord ++ tailWord_2820420).sum := by decide
  have hdescent : baseEnd_2820420 < baseStart_2820420 := by decide
  rcases family_descends (prefixWord ++ tailWord_2820420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2820433 : List Nat := [1, 2, 2, 1, 4, 3, 2, 3, 1, 4]
def baseStart_2820433 : Nat := 118140960795 + 2820433 * 2 ^ 59
def prefixEnd_2820433 : Nat := 4983230072969 + 3 ^ 40 * 2820433 * 2
def baseEnd_2820433 : Nat := 482745927600822925538857

theorem tailTrace_2820433 : CollatzResearch.WordTrace tailWord_2820433 prefixEnd_2820433 482745927600822925538857 := by
  unfold tailWord_2820433
  simp only [CollatzResearch.WordTrace]
  refine ⟨102869642591060407452081953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68579761727373604968054635 102869642591060407452081953)
  ·
    refine ⟨77152231943295305589061465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102869642591060407452081953 77152231943295305589061465)
    ·
      refine ⟨57864173957471479191796099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77152231943295305589061465 57864173957471479191796099)
      ·
        refine ⟨86796260936207218787694149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57864173957471479191796099 86796260936207218787694149)
        ·
          refine ⟨16274298925538853522692653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 86796260936207218787694149 16274298925538853522692653)
          ·
            refine ⟨6102862097077070071009745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16274298925538853522692653 6102862097077070071009745)
            ·
              refine ⟨4577146572807802553257309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6102862097077070071009745 4577146572807802553257309)
              ·
                refine ⟨1716429964802925957471491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4577146572807802553257309 1716429964802925957471491)
                ·
                  refine ⟨2574644947204388936207237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1716429964802925957471491 2574644947204388936207237)
                  ·
                    refine ⟨482745927600822925538857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2574644947204388936207237 482745927600822925538857)
                    ·
                      rfl

theorem cell23_2820433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 2, 3, 1, 4].length) (baseStart_2820433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2820433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2820433 prefixEnd_2820433 := by exact prefixLift 2820433
  have htrace : WordTrace (prefixWord ++ tailWord_2820433) baseStart_2820433 baseEnd_2820433 := by
    simpa [prefixWord, tailWord_2820433, baseEnd_2820433] using wordTrace_append hprefix tailTrace_2820433
  have hstable : (prefixWord ++ tailWord_2820433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2820433).length < 2 ^ (prefixWord ++ tailWord_2820433).sum := by decide
  have hdescent : baseEnd_2820433 < baseStart_2820433 := by decide
  rcases family_descends (prefixWord ++ tailWord_2820433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2820466 : List Nat := [3, 2, 1, 2, 1, 3, 1, 2, 1, 5, 2]
def baseStart_2820466 : Nat := 118140960795 + 2820466 * 2 ^ 59
def prefixEnd_2820466 : Nat := 4983230072969 + 3 ^ 40 * 2820466 * 2
def baseEnd_2820466 : Nat := 1448254727664067147503919

theorem tailTrace_2820466 : CollatzResearch.WordTrace tailWord_2820466 prefixEnd_2820466 1448254727664067147503919 := by
  unfold tailWord_2820466
  simp only [CollatzResearch.WordTrace]
  refine ⟨25717711549985213522008313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68580564133293902725355501 25717711549985213522008313)
  ·
    refine ⟨19288283662488910141506235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25717711549985213522008313 19288283662488910141506235)
    ·
      refine ⟨28932425493733365212259353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19288283662488910141506235 28932425493733365212259353)
      ·
        refine ⟨21699319120300023909194515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28932425493733365212259353 21699319120300023909194515)
        ·
          refine ⟨32548978680450035863791773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21699319120300023909194515 32548978680450035863791773)
          ·
            refine ⟨12205867005168763448921915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32548978680450035863791773 12205867005168763448921915)
            ·
              refine ⟨18308800507753145173382873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12205867005168763448921915 18308800507753145173382873)
              ·
                refine ⟨13731600380814858880037155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18308800507753145173382873 13731600380814858880037155)
                ·
                  refine ⟨20597400571222288320055733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13731600380814858880037155 20597400571222288320055733)
                  ·
                    refine ⟨1931006303552089530005225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 20597400571222288320055733 1931006303552089530005225)
                    ·
                      refine ⟨1448254727664067147503919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1931006303552089530005225 1448254727664067147503919)
                      ·
                        rfl

theorem cell23_2820466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 2, 1, 5, 2].length) (baseStart_2820466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2820466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2820466 prefixEnd_2820466 := by exact prefixLift 2820466
  have htrace : WordTrace (prefixWord ++ tailWord_2820466) baseStart_2820466 baseEnd_2820466 := by
    simpa [prefixWord, tailWord_2820466, baseEnd_2820466] using wordTrace_append hprefix tailTrace_2820466
  have hstable : (prefixWord ++ tailWord_2820466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2820466).length < 2 ^ (prefixWord ++ tailWord_2820466).sum := by decide
  have hdescent : baseEnd_2820466 < baseStart_2820466 := by decide
  rcases family_descends (prefixWord ++ tailWord_2820466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2820500 : List Nat := [2, 4, 2, 1, 3, 1, 1, 2, 2, 3, 2]
def baseStart_2820500 : Nat := 118140960795 + 2820500 * 2 ^ 59
def prefixEnd_2820500 : Nat := 4983230072969 + 3 ^ 40 * 2820500 * 2
def baseEnd_2820500 : Nat := 1448272186006320014478763

theorem tailTrace_2820500 : CollatzResearch.WordTrace tailWord_2820500 prefixEnd_2820500 1448272186006320014478763 := by
  unfold tailWord_2820500
  simp only [CollatzResearch.WordTrace]
  refine ⟨51436043140908838947385477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68581390854545118596513969 51436043140908838947385477)
  ·
    refine ⟨9644258088920407302634777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51436043140908838947385477 9644258088920407302634777)
    ·
      refine ⟨7233193566690305476976083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9644258088920407302634777 7233193566690305476976083)
      ·
        refine ⟨10849790350035458215464125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7233193566690305476976083 10849790350035458215464125)
        ·
          refine ⟨4068671381263296830799047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10849790350035458215464125 4068671381263296830799047)
          ·
            refine ⟨6103007071894945246198571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4068671381263296830799047 6103007071894945246198571)
            ·
              refine ⟨9154510607842417869297857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6103007071894945246198571 9154510607842417869297857)
              ·
                refine ⟨6865882955881813401973393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9154510607842417869297857 6865882955881813401973393)
                ·
                  refine ⟨5149412216911360051480045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6865882955881813401973393 5149412216911360051480045)
                  ·
                    refine ⟨1931029581341760019305017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5149412216911360051480045 1931029581341760019305017)
                    ·
                      refine ⟨1448272186006320014478763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1931029581341760019305017 1448272186006320014478763)
                      ·
                        rfl

theorem cell23_2820500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 1, 2, 2, 3, 2].length) (baseStart_2820500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2820500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2820500 prefixEnd_2820500 := by exact prefixLift 2820500
  have htrace : WordTrace (prefixWord ++ tailWord_2820500) baseStart_2820500 baseEnd_2820500 := by
    simpa [prefixWord, tailWord_2820500, baseEnd_2820500] using wordTrace_append hprefix tailTrace_2820500
  have hstable : (prefixWord ++ tailWord_2820500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2820500).length < 2 ^ (prefixWord ++ tailWord_2820500).sum := by decide
  have hdescent : baseEnd_2820500 < baseStart_2820500 := by decide
  rcases family_descends (prefixWord ++ tailWord_2820500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2820506 : List Nat := [3, 1, 1, 4, 1, 2, 2, 1, 4, 4]
def baseStart_2820506 : Nat := 118140960795 + 2820506 * 2 ^ 59
def prefixEnd_2820506 : Nat := 4983230072969 + 3 ^ 40 * 2820506 * 2
def baseEnd_2820506 : Nat := 482758422296748997001245

theorem tailTrace_2820506 : CollatzResearch.WordTrace tailWord_2820506 prefixEnd_2820506 482758422296748997001245 := by
  unfold tailWord_2820506
  simp only [CollatzResearch.WordTrace]
  refine ⟨25718076279948985229872343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68581536746530627279659581 25718076279948985229872343)
  ·
    refine ⟨38577114419923477844808515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25718076279948985229872343 38577114419923477844808515)
    ·
      refine ⟨57865671629885216767212773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38577114419923477844808515 57865671629885216767212773)
      ·
        refine ⟨10849813430603478143852395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57865671629885216767212773 10849813430603478143852395)
        ·
          refine ⟨16274720145905217215778593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10849813430603478143852395 16274720145905217215778593)
          ·
            refine ⟨12206040109428912911833945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16274720145905217215778593 12206040109428912911833945)
            ·
              refine ⟨9154530082071684683875459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12206040109428912911833945 9154530082071684683875459)
              ·
                refine ⟨13731795123107527025813189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9154530082071684683875459 13731795123107527025813189)
                ·
                  refine ⟨2574711585582661317339973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13731795123107527025813189 2574711585582661317339973)
                  ·
                    refine ⟨482758422296748997001245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2574711585582661317339973 482758422296748997001245)
                    ·
                      rfl

theorem cell23_2820506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 2, 1, 4, 4].length) (baseStart_2820506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2820506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2820506 prefixEnd_2820506 := by exact prefixLift 2820506
  have htrace : WordTrace (prefixWord ++ tailWord_2820506) baseStart_2820506 baseEnd_2820506 := by
    simpa [prefixWord, tailWord_2820506, baseEnd_2820506] using wordTrace_append hprefix tailTrace_2820506
  have hstable : (prefixWord ++ tailWord_2820506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2820506).length < 2 ^ (prefixWord ++ tailWord_2820506).sum := by decide
  have hdescent : baseEnd_2820506 < baseStart_2820506 := by decide
  rcases family_descends (prefixWord ++ tailWord_2820506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2820519 : List Nat := [1, 1, 6, 1, 1, 2, 1, 10]
def baseStart_2820519 : Nat := 118140960795 + 2820519 * 2 ^ 59
def prefixEnd_2820519 : Nat := 4983230072969 + 3 ^ 40 * 2820519 * 2
def baseEnd_2820519 : Nat := 53640071931065016301525

theorem tailTrace_2820519 : CollatzResearch.WordTrace tailWord_2820519 prefixEnd_2820519 53640071931065016301525 := by
  unfold tailWord_2820519
  simp only [CollatzResearch.WordTrace]
  refine ⟨102872779268748844139712611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68581852845832562759808407 102872779268748844139712611)
  ·
    refine ⟨154309168903123266209568917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102872779268748844139712611 154309168903123266209568917)
    ·
      refine ⟨7233242292333903103573543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 154309168903123266209568917 7233242292333903103573543)
      ·
        refine ⟨10849863438500854655360315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7233242292333903103573543 10849863438500854655360315)
        ·
          refine ⟨16274795157751281983040473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10849863438500854655360315 16274795157751281983040473)
          ·
            refine ⟨12206096368313461487280355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16274795157751281983040473 12206096368313461487280355)
            ·
              refine ⟨18309144552470192230920533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12206096368313461487280355 18309144552470192230920533)
              ·
                refine ⟨53640071931065016301525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 18309144552470192230920533 53640071931065016301525)
                ·
                  rfl

theorem cell23_2820519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 10].length) (baseStart_2820519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2820519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2820519 prefixEnd_2820519 := by exact prefixLift 2820519
  have htrace : WordTrace (prefixWord ++ tailWord_2820519) baseStart_2820519 baseEnd_2820519 := by
    simpa [prefixWord, tailWord_2820519, baseEnd_2820519] using wordTrace_append hprefix tailTrace_2820519
  have hstable : (prefixWord ++ tailWord_2820519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2820519).length < 2 ^ (prefixWord ++ tailWord_2820519).sum := by decide
  have hdescent : baseEnd_2820519 < baseStart_2820519 := by decide
  rcases family_descends (prefixWord ++ tailWord_2820519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2820533 : List Nat := [1, 3, 3, 2, 3, 1, 1, 1, 3, 2, 3]
def baseStart_2820533 : Nat := 118140960795 + 2820533 * 2 ^ 59
def prefixEnd_2820533 : Nat := 4983230072969 + 3 ^ 40 * 2820533 * 2
def baseEnd_2820533 : Nat := 1448289130867918385366111

theorem tailTrace_2820533 : CollatzResearch.WordTrace tailWord_2820533 prefixEnd_2820533 1448289130867918385366111 := by
  unfold tailWord_2820533
  simp only [CollatzResearch.WordTrace]
  refine ⟨102873289890698124530722253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68582193260465416353814835 102873289890698124530722253)
  ·
    refine ⟨38577483709011796699020845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102873289890698124530722253 38577483709011796699020845)
    ·
      refine ⟨14466556390879423762132817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38577483709011796699020845 14466556390879423762132817)
      ·
        refine ⟨10849917293159567821599613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14466556390879423762132817 10849917293159567821599613)
        ·
          refine ⟨4068718984934837933099855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10849917293159567821599613 4068718984934837933099855)
          ·
            refine ⟨6103078477402256899649783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4068718984934837933099855 6103078477402256899649783)
            ·
              refine ⟨9154617716103385349474675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6103078477402256899649783 9154617716103385349474675)
              ·
                refine ⟨13731926574155078024212013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9154617716103385349474675 13731926574155078024212013)
                ·
                  refine ⟨5149472465308154259079505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13731926574155078024212013 5149472465308154259079505)
                  ·
                    refine ⟨3862104348981115694309629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5149472465308154259079505 3862104348981115694309629)
                    ·
                      refine ⟨1448289130867918385366111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3862104348981115694309629 1448289130867918385366111)
                      ·
                        rfl

theorem cell23_2820533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 1, 1, 3, 2, 3].length) (baseStart_2820533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2820533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2820533 prefixEnd_2820533 := by exact prefixLift 2820533
  have htrace : WordTrace (prefixWord ++ tailWord_2820533) baseStart_2820533 baseEnd_2820533 := by
    simpa [prefixWord, tailWord_2820533, baseEnd_2820533] using wordTrace_append hprefix tailTrace_2820533
  have hstable : (prefixWord ++ tailWord_2820533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2820533).length < 2 ^ (prefixWord ++ tailWord_2820533).sum := by decide
  have hdescent : baseEnd_2820533 < baseStart_2820533 := by decide
  rcases family_descends (prefixWord ++ tailWord_2820533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2820564 : List Nat := [2, 4, 1, 2, 2, 1, 4, 2, 1, 2, 2]
def baseStart_2820564 : Nat := 118140960795 + 2820564 * 2 ^ 59
def prefixEnd_2820564 : Nat := 4983230072969 + 3 ^ 40 * 2820564 * 2
def baseEnd_2820564 : Nat := 1448305048768207764078469

theorem tailTrace_2820564 : CollatzResearch.WordTrace tailWord_2820564 prefixEnd_2820564 1448305048768207764078469 := by
  unfold tailWord_2820564
  simp only [CollatzResearch.WordTrace]
  refine ⟨51437210276792908412550373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68582947035723877883400497 51437210276792908412550373)
  ·
    refine ⟨9644476926898670327353195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51437210276792908412550373 9644476926898670327353195)
    ·
      refine ⟨14466715390348005491029793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9644476926898670327353195 14466715390348005491029793)
      ·
        refine ⟨10850036542761004118272345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14466715390348005491029793 10850036542761004118272345)
        ·
          refine ⟨8137527407070753088704259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10850036542761004118272345 8137527407070753088704259)
          ·
            refine ⟨12206291110606129633056389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8137527407070753088704259 12206291110606129633056389)
            ·
              refine ⟨2288679583238649306198073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12206291110606129633056389 2288679583238649306198073)
              ·
                refine ⟨1716509687428986979648555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2288679583238649306198073 1716509687428986979648555)
                ·
                  refine ⟨2574764531143480469472833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1716509687428986979648555 2574764531143480469472833)
                  ·
                    refine ⟨1931073398357610352104625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2574764531143480469472833 1931073398357610352104625)
                    ·
                      refine ⟨1448305048768207764078469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1931073398357610352104625 1448305048768207764078469)
                      ·
                        rfl

theorem cell23_2820564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 4, 2, 1, 2, 2].length) (baseStart_2820564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2820564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2820564 prefixEnd_2820564 := by exact prefixLift 2820564
  have htrace : WordTrace (prefixWord ++ tailWord_2820564) baseStart_2820564 baseEnd_2820564 := by
    simpa [prefixWord, tailWord_2820564, baseEnd_2820564] using wordTrace_append hprefix tailTrace_2820564
  have hstable : (prefixWord ++ tailWord_2820564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2820564).length < 2 ^ (prefixWord ++ tailWord_2820564).sum := by decide
  have hdescent : baseEnd_2820564 < baseStart_2820564 := by decide
  rcases family_descends (prefixWord ++ tailWord_2820564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2820566 : List Nat := [5, 2, 1, 1, 1, 1, 1, 1, 1, 9]
def baseStart_2820566 : Nat := 118140960795 + 2820566 * 2 ^ 59
def prefixEnd_2820566 : Nat := 4983230072969 + 3 ^ 40 * 2820566 * 2
def baseEnd_2820566 : Nat := 482768691909838918751153

theorem tailTrace_2820566 : CollatzResearch.WordTrace tailWord_2820566 prefixEnd_2820566 482768691909838918751153 := by
  unfold tailWord_2820566
  simp only [CollatzResearch.WordTrace]
  refine ⟨6429655843723660697917097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 68582995666385714111115701 6429655843723660697917097)
  ·
    refine ⟨4822241882792745523437823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6429655843723660697917097 4822241882792745523437823)
    ·
      refine ⟨7233362824189118285156735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4822241882792745523437823 7233362824189118285156735)
      ·
        refine ⟨10850044236283677427735103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7233362824189118285156735 10850044236283677427735103)
        ·
          refine ⟨16275066354425516141602655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10850044236283677427735103 16275066354425516141602655)
          ·
            refine ⟨24412599531638274212403983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16275066354425516141602655 24412599531638274212403983)
            ·
              refine ⟨36618899297457411318605975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24412599531638274212403983 36618899297457411318605975)
              ·
                refine ⟨54928348946186116977908963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36618899297457411318605975 54928348946186116977908963)
                ·
                  refine ⟨82392523419279175466863445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54928348946186116977908963 82392523419279175466863445)
                  ·
                    refine ⟨482768691909838918751153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 82392523419279175466863445 482768691909838918751153)
                    ·
                      rfl

theorem cell23_2820566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 1, 1, 9].length) (baseStart_2820566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2820566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2820566 prefixEnd_2820566 := by exact prefixLift 2820566
  have htrace : WordTrace (prefixWord ++ tailWord_2820566) baseStart_2820566 baseEnd_2820566 := by
    simpa [prefixWord, tailWord_2820566, baseEnd_2820566] using wordTrace_append hprefix tailTrace_2820566
  have hstable : (prefixWord ++ tailWord_2820566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2820566).length < 2 ^ (prefixWord ++ tailWord_2820566).sum := by decide
  have hdescent : baseEnd_2820566 < baseStart_2820566 := by decide
  rcases family_descends (prefixWord ++ tailWord_2820566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2820569 : List Nat := [1, 2, 1, 2, 4, 1, 1, 1, 1, 5, 4]
def baseStart_2820569 : Nat := 118140960795 + 2820569 * 2 ^ 59
def prefixEnd_2820569 : Nat := 4983230072969 + 3 ^ 40 * 2820569 * 2
def baseEnd_2820569 : Nat := 1448307616171480244515945

theorem tailTrace_2820569 : CollatzResearch.WordTrace tailWord_2820569 prefixEnd_2820569 1448307616171480244515945 := by
  unfold tailWord_2820569
  simp only [CollatzResearch.WordTrace]
  refine ⟨102874602918567702679032761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68583068612378468452688507 102874602918567702679032761)
  ·
    refine ⟨77155952188925777009274571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102874602918567702679032761 77155952188925777009274571)
    ·
      refine ⟨115733928283388665513911857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77155952188925777009274571 115733928283388665513911857)
      ·
        refine ⟨86800446212541499135433893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115733928283388665513911857 86800446212541499135433893)
        ·
          refine ⟨16275083664851531087893855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 86800446212541499135433893 16275083664851531087893855)
          ·
            refine ⟨24412625497277296631840783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16275083664851531087893855 24412625497277296631840783)
            ·
              refine ⟨36618938245915944947761175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24412625497277296631840783 36618938245915944947761175)
              ·
                refine ⟨54928407368873917421641763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36618938245915944947761175 54928407368873917421641763)
                ·
                  refine ⟨82392611053310876132462645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54928407368873917421641763 82392611053310876132462645)
                  ·
                    refine ⟨7724307286247894637418373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 82392611053310876132462645 7724307286247894637418373)
                    ·
                      refine ⟨1448307616171480244515945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7724307286247894637418373 1448307616171480244515945)
                      ·
                        rfl

theorem cell23_2820569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 1, 1, 5, 4].length) (baseStart_2820569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2820569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2820569 prefixEnd_2820569 := by exact prefixLift 2820569
  have htrace : WordTrace (prefixWord ++ tailWord_2820569) baseStart_2820569 baseEnd_2820569 := by
    simpa [prefixWord, tailWord_2820569, baseEnd_2820569] using wordTrace_append hprefix tailTrace_2820569
  have hstable : (prefixWord ++ tailWord_2820569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2820569).length < 2 ^ (prefixWord ++ tailWord_2820569).sum := by decide
  have hdescent : baseEnd_2820569 < baseStart_2820569 := by decide
  rcases family_descends (prefixWord ++ tailWord_2820569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2820573 : List Nat := [1, 4, 3, 1, 1, 1, 1, 1, 5, 3, 2]
def baseStart_2820573 : Nat := 118140960795 + 2820573 * 2 ^ 59
def prefixEnd_2820573 : Nat := 4983230072969 + 3 ^ 40 * 2820573 * 2
def baseEnd_2820573 : Nat := 1448309670094098228865927

theorem tailTrace_2820573 : CollatzResearch.WordTrace tailWord_2820573 prefixEnd_2820573 1448309670094098228865927 := by
  unfold tailWord_2820573
  simp only [CollatzResearch.WordTrace]
  refine ⟨102874748810553211362178373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68583165873702140908118915 102874748810553211362178373)
  ·
    refine ⟨19289015401978727130408445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 102874748810553211362178373 19289015401978727130408445)
    ·
      refine ⟨7233380775742022673903167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19289015401978727130408445 7233380775742022673903167)
      ·
        refine ⟨10850071163613034010854751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7233380775742022673903167 10850071163613034010854751)
        ·
          refine ⟨16275106745419551016282127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10850071163613034010854751 16275106745419551016282127)
          ·
            refine ⟨24412660118129326524423191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16275106745419551016282127 24412660118129326524423191)
            ·
              refine ⟨36618990177193989786634787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24412660118129326524423191 36618990177193989786634787)
              ·
                refine ⟨54928485265790984679952181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36618990177193989786634787 54928485265790984679952181)
                ·
                  refine ⟨5149545493667904813745517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 54928485265790984679952181 5149545493667904813745517)
                  ·
                    refine ⟨1931079560125464305154569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5149545493667904813745517 1931079560125464305154569)
                    ·
                      refine ⟨1448309670094098228865927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1931079560125464305154569 1448309670094098228865927)
                      ·
                        rfl

theorem cell23_2820573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 1, 5, 3, 2].length) (baseStart_2820573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2820573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2820573 prefixEnd_2820573 := by exact prefixLift 2820573
  have htrace : WordTrace (prefixWord ++ tailWord_2820573) baseStart_2820573 baseEnd_2820573 := by
    simpa [prefixWord, tailWord_2820573, baseEnd_2820573] using wordTrace_append hprefix tailTrace_2820573
  have hstable : (prefixWord ++ tailWord_2820573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2820573).length < 2 ^ (prefixWord ++ tailWord_2820573).sum := by decide
  have hdescent : baseEnd_2820573 < baseStart_2820573 := by decide
  rcases family_descends (prefixWord ++ tailWord_2820573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2820614 : List Nat := [6, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3]
def baseStart_2820614 : Nat := 118140960795 + 2820614 * 2 ^ 59
def prefixEnd_2820614 : Nat := 4983230072969 + 3 ^ 40 * 2820614 * 2
def baseEnd_2820614 : Nat := 1448330722800932568453239

theorem tailTrace_2820614 : CollatzResearch.WordTrace tailWord_2820614 prefixEnd_2820614 1448330722800932568453239 := by
  unfold tailWord_2820614
  simp only [CollatzResearch.WordTrace]
  refine ⟨3214882631356396105138153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 68584162802269783576280597 3214882631356396105138153)
  ·
    refine ⟨2411161973517297078853615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3214882631356396105138153 2411161973517297078853615)
    ·
      refine ⟨3616742960275945618280423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2411161973517297078853615 3616742960275945618280423)
      ·
        refine ⟨5425114440413918427420635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3616742960275945618280423 5425114440413918427420635)
        ·
          refine ⟨8137671660620877641130953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5425114440413918427420635 8137671660620877641130953)
          ·
            refine ⟨6103253745465658230848215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8137671660620877641130953 6103253745465658230848215)
            ·
              refine ⟨9154880618198487346272323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6103253745465658230848215 9154880618198487346272323)
              ·
                refine ⟨13732320927297731019408485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9154880618198487346272323 13732320927297731019408485)
                ·
                  refine ⟨2574810173868324566139091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13732320927297731019408485 2574810173868324566139091)
                  ·
                    refine ⟨3862215260802486849208637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2574810173868324566139091 3862215260802486849208637)
                    ·
                      refine ⟨1448330722800932568453239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3862215260802486849208637 1448330722800932568453239)
                      ·
                        rfl

theorem cell23_2820614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3].length) (baseStart_2820614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2820614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2820614 prefixEnd_2820614 := by exact prefixLift 2820614
  have htrace : WordTrace (prefixWord ++ tailWord_2820614) baseStart_2820614 baseEnd_2820614 := by
    simpa [prefixWord, tailWord_2820614, baseEnd_2820614] using wordTrace_append hprefix tailTrace_2820614
  have hstable : (prefixWord ++ tailWord_2820614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2820614).length < 2 ^ (prefixWord ++ tailWord_2820614).sum := by decide
  have hdescent : baseEnd_2820614 < baseStart_2820614 := by decide
  rcases family_descends (prefixWord ++ tailWord_2820614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2820620 : List Nat := [2, 2, 1, 2, 4, 2, 1, 1, 4, 2, 2]
def baseStart_2820620 : Nat := 118140960795 + 2820620 * 2 ^ 59
def prefixEnd_2820620 : Nat := 4983230072969 + 3 ^ 40 * 2820620 * 2
def baseEnd_2820620 : Nat := 1448333803684859544978211

theorem tailTrace_2820620 : CollatzResearch.WordTrace tailWord_2820620 prefixEnd_2820620 1448333803684859544978211 := by
  unfold tailWord_2820620
  simp only [CollatzResearch.WordTrace]
  refine ⟨51438231520691469194569657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68584308694255292259426209 51438231520691469194569657)
  ·
    refine ⟨38578673640518601895927243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51438231520691469194569657 38578673640518601895927243)
    ·
      refine ⟨57868010460777902843890865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38578673640518601895927243 57868010460777902843890865)
      ·
        refine ⟨43401007845583427132918149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57868010460777902843890865 43401007845583427132918149)
        ·
          refine ⟨8137688971046892587422153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43401007845583427132918149 8137688971046892587422153)
          ·
            refine ⟨6103266728285169440566615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8137688971046892587422153 6103266728285169440566615)
            ·
              refine ⟨9154900092427754160849923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6103266728285169440566615 9154900092427754160849923)
              ·
                refine ⟨13732350138641631241274885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9154900092427754160849923 13732350138641631241274885)
                ·
                  refine ⟨2574815650995305857739041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13732350138641631241274885 2574815650995305857739041)
                  ·
                    refine ⟨1931111738246479393304281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2574815650995305857739041 1931111738246479393304281)
                    ·
                      refine ⟨1448333803684859544978211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1931111738246479393304281 1448333803684859544978211)
                      ·
                        rfl

theorem cell23_2820620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 1, 1, 4, 2, 2].length) (baseStart_2820620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2820620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2820620 prefixEnd_2820620 := by exact prefixLift 2820620
  have htrace : WordTrace (prefixWord ++ tailWord_2820620) baseStart_2820620 baseEnd_2820620 := by
    simpa [prefixWord, tailWord_2820620, baseEnd_2820620] using wordTrace_append hprefix tailTrace_2820620
  have hstable : (prefixWord ++ tailWord_2820620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2820620).length < 2 ^ (prefixWord ++ tailWord_2820620).sum := by decide
  have hdescent : baseEnd_2820620 < baseStart_2820620 := by decide
  rcases family_descends (prefixWord ++ tailWord_2820620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2820673 : List Nat := [1, 2, 5, 1, 1, 3, 1, 2, 2, 5]
def baseStart_2820673 : Nat := 118140960795 + 2820673 * 2 ^ 59
def prefixEnd_2820673 : Nat := 4983230072969 + 3 ^ 40 * 2820673 * 2
def baseEnd_2820673 : Nat := 482787006053182612538489

theorem tailTrace_2820673 : CollatzResearch.WordTrace tailWord_2820673 prefixEnd_2820673 482787006053182612538489 := by
  unfold tailWord_2820673
  simp only [CollatzResearch.WordTrace]
  refine ⟨102878396110190928440818673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68585597406793952293879115 102878396110190928440818673)
  ·
    refine ⟨77158797082643196330614005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102878396110190928440818673 77158797082643196330614005)
    ·
      refine ⟨7233637226497799655995063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 77158797082643196330614005 7233637226497799655995063)
      ·
        refine ⟨10850455839746699483992595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7233637226497799655995063 10850455839746699483992595)
        ·
          refine ⟨16275683759620049225988893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10850455839746699483992595 16275683759620049225988893)
          ·
            refine ⟨6103381409857518459745835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16275683759620049225988893 6103381409857518459745835)
            ·
              refine ⟨9155072114786277689618753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6103381409857518459745835 9155072114786277689618753)
              ·
                refine ⟨6866304086089708267214065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9155072114786277689618753 6866304086089708267214065)
                ·
                  refine ⟨5149728064567281200410549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6866304086089708267214065 5149728064567281200410549)
                  ·
                    refine ⟨482787006053182612538489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5149728064567281200410549 482787006053182612538489)
                    ·
                      rfl

theorem cell23_2820673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 1, 2, 2, 5].length) (baseStart_2820673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2820673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2820673 prefixEnd_2820673 := by exact prefixLift 2820673
  have htrace : WordTrace (prefixWord ++ tailWord_2820673) baseStart_2820673 baseEnd_2820673 := by
    simpa [prefixWord, tailWord_2820673, baseEnd_2820673] using wordTrace_append hprefix tailTrace_2820673
  have hstable : (prefixWord ++ tailWord_2820673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2820673).length < 2 ^ (prefixWord ++ tailWord_2820673).sum := by decide
  have hdescent : baseEnd_2820673 < baseStart_2820673 := by decide
  rcases family_descends (prefixWord ++ tailWord_2820673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2820693 : List Nat := [1, 3, 2, 2, 1, 1, 2, 3, 2, 4, 2]
def baseStart_2820693 : Nat := 118140960795 + 2820693 * 2 ^ 59
def prefixEnd_2820693 : Nat := 4983230072969 + 3 ^ 40 * 2820693 * 2
def baseEnd_2820693 : Nat := 1448371287772637759365375

theorem tailTrace_2820693 : CollatzResearch.WordTrace tailWord_2820693 prefixEnd_2820693 1448371287772637759365375 := by
  unfold tailWord_2820693
  simp only [CollatzResearch.WordTrace]
  refine ⟨102879125570118471856546733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68586083713412314571031155 102879125570118471856546733)
  ·
    refine ⟨38579672088794426946205025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102879125570118471856546733 38579672088794426946205025)
    ·
      refine ⟨28934754066595820209653769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38579672088794426946205025 28934754066595820209653769)
      ·
        refine ⟨21701065549946865157240327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28934754066595820209653769 21701065549946865157240327)
        ·
          refine ⟨32551598324920297735860491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21701065549946865157240327 32551598324920297735860491)
          ·
            refine ⟨48827397487380446603790737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32551598324920297735860491 48827397487380446603790737)
            ·
              refine ⟨36620548115535334952843053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48827397487380446603790737 36620548115535334952843053)
              ·
                refine ⟨13732705543325750607316145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36620548115535334952843053 13732705543325750607316145)
                ·
                  refine ⟨10299529157494312955487109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13732705543325750607316145 10299529157494312955487109)
                  ·
                    refine ⟨1931161717030183679153833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10299529157494312955487109 1931161717030183679153833)
                    ·
                      refine ⟨1448371287772637759365375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1931161717030183679153833 1448371287772637759365375)
                      ·
                        rfl

theorem cell23_2820693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 3, 2, 4, 2].length) (baseStart_2820693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2820693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2820693 prefixEnd_2820693 := by exact prefixLift 2820693
  have htrace : WordTrace (prefixWord ++ tailWord_2820693) baseStart_2820693 baseEnd_2820693 := by
    simpa [prefixWord, tailWord_2820693, baseEnd_2820693] using wordTrace_append hprefix tailTrace_2820693
  have hstable : (prefixWord ++ tailWord_2820693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2820693).length < 2 ^ (prefixWord ++ tailWord_2820693).sum := by decide
  have hdescent : baseEnd_2820693 < baseStart_2820693 := by decide
  rcases family_descends (prefixWord ++ tailWord_2820693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2820696 : List Nat := [2, 1, 2, 2, 1, 2, 2, 1, 3, 4, 3]
def baseStart_2820696 : Nat := 118140960795 + 2820696 * 2 ^ 59
def prefixEnd_2820696 : Nat := 4983230072969 + 3 ^ 40 * 2820696 * 2
def baseEnd_2820696 : Nat := 1448372828214601247627861

theorem tailTrace_2820696 : CollatzResearch.WordTrace tailWord_2820696 prefixEnd_2820696 1448372828214601247627861 := by
  unfold tailWord_2820696
  simp only [CollatzResearch.WordTrace]
  refine ⟨51439617494553801684452971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68586156659405068912603961 51439617494553801684452971)
  ·
    refine ⟨77159426241830702526679457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51439617494553801684452971 77159426241830702526679457)
    ·
      refine ⟨57869569681373026895009593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77159426241830702526679457 57869569681373026895009593)
      ·
        refine ⟨43402177261029770171257195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57869569681373026895009593 43402177261029770171257195)
        ·
          refine ⟨65103265891544655256885793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43402177261029770171257195 65103265891544655256885793)
          ·
            refine ⟨48827449418658491442664345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65103265891544655256885793 48827449418658491442664345)
            ·
              refine ⟨36620587063993868581998259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48827449418658491442664345 36620587063993868581998259)
              ·
                refine ⟨54930880595990802872997389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36620587063993868581998259 54930880595990802872997389)
                ·
                  refine ⟨20599080223496551077374021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54930880595990802872997389 20599080223496551077374021)
                  ·
                    refine ⟨3862327541905603327007629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20599080223496551077374021 3862327541905603327007629)
                    ·
                      refine ⟨1448372828214601247627861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3862327541905603327007629 1448372828214601247627861)
                      ·
                        rfl

theorem cell23_2820696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 1, 3, 4, 3].length) (baseStart_2820696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2820696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2820696 prefixEnd_2820696 := by exact prefixLift 2820696
  have htrace : WordTrace (prefixWord ++ tailWord_2820696) baseStart_2820696 baseEnd_2820696 := by
    simpa [prefixWord, tailWord_2820696, baseEnd_2820696] using wordTrace_append hprefix tailTrace_2820696
  have hstable : (prefixWord ++ tailWord_2820696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2820696).length < 2 ^ (prefixWord ++ tailWord_2820696).sum := by decide
  have hdescent : baseEnd_2820696 < baseStart_2820696 := by decide
  rcases family_descends (prefixWord ++ tailWord_2820696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2820760 : List Nat := [2, 1, 2, 4, 1, 1, 3, 2, 3, 1, 3]
def baseStart_2820760 : Nat := 118140960795 + 2820760 * 2 ^ 59
def prefixEnd_2820760 : Nat := 4983230072969 + 3 ^ 40 * 2820760 * 2
def baseEnd_2820760 : Nat := 1448405690976488997227567

theorem tailTrace_2820760 : CollatzResearch.WordTrace tailWord_2820760 prefixEnd_2820760 1448405690976488997227567 := by
  unfold tailWord_2820760
  simp only [CollatzResearch.WordTrace]
  refine ⟨51440784630437871149617867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68587712840583828199490489 51440784630437871149617867)
  ·
    refine ⟨77161176945656806724426801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51440784630437871149617867 77161176945656806724426801)
    ·
      refine ⟨57870882709242605043320101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77161176945656806724426801 57870882709242605043320101)
      ·
        refine ⟨10850790507982988445622519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57870882709242605043320101 10850790507982988445622519)
        ·
          refine ⟨16276185761974482668433779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10850790507982988445622519 16276185761974482668433779)
          ·
            refine ⟨24414278642961724002650669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16276185761974482668433779 24414278642961724002650669)
            ·
              refine ⟨9155354491110646500994001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24414278642961724002650669 9155354491110646500994001)
              ·
                refine ⟨6866515868332984875745501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9155354491110646500994001 6866515868332984875745501)
                ·
                  refine ⟨2574943450624869328404563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6866515868332984875745501 2574943450624869328404563)
                  ·
                    refine ⟨3862415175937303992606845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2574943450624869328404563 3862415175937303992606845)
                    ·
                      refine ⟨1448405690976488997227567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3862415175937303992606845 1448405690976488997227567)
                      ·
                        rfl

theorem cell23_2820760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 3, 2, 3, 1, 3].length) (baseStart_2820760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2820760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2820760 prefixEnd_2820760 := by exact prefixLift 2820760
  have htrace : WordTrace (prefixWord ++ tailWord_2820760) baseStart_2820760 baseEnd_2820760 := by
    simpa [prefixWord, tailWord_2820760, baseEnd_2820760] using wordTrace_append hprefix tailTrace_2820760
  have hstable : (prefixWord ++ tailWord_2820760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2820760).length < 2 ^ (prefixWord ++ tailWord_2820760).sum := by decide
  have hdescent : baseEnd_2820760 < baseStart_2820760 := by decide
  rcases family_descends (prefixWord ++ tailWord_2820760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2820810 : List Nat := [3, 1, 2, 1, 4, 3, 1, 1, 1, 6]
def baseStart_2820810 : Nat := 118140960795 + 2820810 * 2 ^ 59
def prefixEnd_2820810 : Nat := 4983230072969 + 3 ^ 40 * 2820810 * 2
def baseEnd_2820810 : Nat := 482810455003071267200779

theorem tailTrace_2820810 : CollatzResearch.WordTrace tailWord_2820810 prefixEnd_2820810 482810455003071267200779 := by
  unfold tailWord_2820810
  simp only [CollatzResearch.WordTrace]
  refine ⟨25720848227673650209638971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68588928607129733892370589 25720848227673650209638971)
  ·
    refine ⟨38581272341510475314458457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25720848227673650209638971 38581272341510475314458457)
    ·
      refine ⟨28935954256132856485843843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38581272341510475314458457 28935954256132856485843843)
      ·
        refine ⟨43403931384199284728765765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28935954256132856485843843 43403931384199284728765765)
        ·
          refine ⟨8138237134537365886643581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43403931384199284728765765 8138237134537365886643581)
          ·
            refine ⟨3051838925451512207491343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8138237134537365886643581 3051838925451512207491343)
            ·
              refine ⟨4577758388177268311237015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3051838925451512207491343 4577758388177268311237015)
              ·
                refine ⟨6866637582265902466855523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4577758388177268311237015 6866637582265902466855523)
                ·
                  refine ⟨10299956373398853700283285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6866637582265902466855523 10299956373398853700283285)
                  ·
                    refine ⟨482810455003071267200779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10299956373398853700283285 482810455003071267200779)
                    ·
                      rfl

theorem cell23_2820810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 1, 1, 1, 6].length) (baseStart_2820810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2820810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2820810 prefixEnd_2820810 := by exact prefixLift 2820810
  have htrace : WordTrace (prefixWord ++ tailWord_2820810) baseStart_2820810 baseEnd_2820810 := by
    simpa [prefixWord, tailWord_2820810, baseEnd_2820810] using wordTrace_append hprefix tailTrace_2820810
  have hstable : (prefixWord ++ tailWord_2820810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2820810).length < 2 ^ (prefixWord ++ tailWord_2820810).sum := by decide
  have hdescent : baseEnd_2820810 < baseStart_2820810 := by decide
  rcases family_descends (prefixWord ++ tailWord_2820810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2820823 : List Nat := [1, 1, 3, 2, 1, 4, 4, 7]
def baseStart_2820823 : Nat := 118140960795 + 2820823 * 2 ^ 59
def prefixEnd_2820823 : Nat := 4983230072969 + 3 ^ 40 * 2820823 * 2
def baseEnd_2820823 : Nat := 53645853342878601879251

theorem tailTrace_2820823 : CollatzResearch.WordTrace tailWord_2820823 prefixEnd_2820823 53645853342878601879251 := by
  unfold tailWord_2820823
  simp only [CollatzResearch.WordTrace]
  refine ⟨102883867059647504058779123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68589244706431669372519415 102883867059647504058779123)
  ·
    refine ⟨154325800589471256088168685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102883867059647504058779123 154325800589471256088168685)
    ·
      refine ⟨57872175221051721033063257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 154325800589471256088168685 57872175221051721033063257)
      ·
        refine ⟨43404131415788790774797443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57872175221051721033063257 43404131415788790774797443)
        ·
          refine ⟨65106197123683186162196165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43404131415788790774797443 65106197123683186162196165)
          ·
            refine ⟨12207411960690597405411781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 65106197123683186162196165 12207411960690597405411781)
            ·
              refine ⟨2288889742629487013514709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12207411960690597405411781 2288889742629487013514709)
              ·
                refine ⟨53645853342878601879251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2288889742629487013514709 53645853342878601879251)
                ·
                  rfl

theorem cell23_2820823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 4, 7].length) (baseStart_2820823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2820823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2820823 prefixEnd_2820823 := by exact prefixLift 2820823
  have htrace : WordTrace (prefixWord ++ tailWord_2820823) baseStart_2820823 baseEnd_2820823 := by
    simpa [prefixWord, tailWord_2820823, baseEnd_2820823] using wordTrace_append hprefix tailTrace_2820823
  have hstable : (prefixWord ++ tailWord_2820823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2820823).length < 2 ^ (prefixWord ++ tailWord_2820823).sum := by decide
  have hdescent : baseEnd_2820823 < baseStart_2820823 := by decide
  rcases family_descends (prefixWord ++ tailWord_2820823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2820840 : List Nat := [2, 1, 4, 1, 5, 1, 9]
def baseStart_2820840 : Nat := 118140960795 + 2820840 * 2 ^ 59
def prefixEnd_2820840 : Nat := 4983230072969 + 3 ^ 40 * 2820840 * 2
def baseEnd_2820840 : Nat := 17882058881837638076879

theorem tailTrace_2820840 : CollatzResearch.WordTrace tailWord_2820840 prefixEnd_2820840 17882058881837638076879 := by
  unfold tailWord_2820840
  simp only [CollatzResearch.WordTrace]
  refine ⟨51442243550292957981073987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68589658067057277308098649 51442243550292957981073987)
  ·
    refine ⟨77163365325439436971610981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51442243550292957981073987 77163365325439436971610981)
    ·
      refine ⟨14468130998519894432177059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 77163365325439436971610981 14468130998519894432177059)
      ·
        refine ⟨21702196497779841648265589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14468130998519894432177059 21702196497779841648265589)
        ·
          refine ⟨2034580921666860154524899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21702196497779841648265589 2034580921666860154524899)
          ·
            refine ⟨3051871382500290231787349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2034580921666860154524899 3051871382500290231787349)
            ·
              refine ⟨17882058881837638076879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3051871382500290231787349 17882058881837638076879)
              ·
                rfl

theorem cell23_2820840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 9].length) (baseStart_2820840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2820840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2820840 prefixEnd_2820840 := by exact prefixLift 2820840
  have htrace : WordTrace (prefixWord ++ tailWord_2820840) baseStart_2820840 baseEnd_2820840 := by
    simpa [prefixWord, tailWord_2820840, baseEnd_2820840] using wordTrace_append hprefix tailTrace_2820840
  have hstable : (prefixWord ++ tailWord_2820840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2820840).length < 2 ^ (prefixWord ++ tailWord_2820840).sum := by decide
  have hdescent : baseEnd_2820840 < baseStart_2820840 := by decide
  rcases family_descends (prefixWord ++ tailWord_2820840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2820907 : List Nat := [1, 1, 1, 1, 2, 1, 2, 8, 2, 2, 2]
def baseStart_2820907 : Nat := 118140960795 + 2820907 * 2 ^ 59
def prefixEnd_2820907 : Nat := 4983230072969 + 3 ^ 40 * 2820907 * 2
def baseEnd_2820907 : Nat := 1448481172632699922089391

theorem tailTrace_2820907 : CollatzResearch.WordTrace tailWord_2820907 prefixEnd_2820907 1448481172632699922089391 := by
  unfold tailWord_2820907
  simp only [CollatzResearch.WordTrace]
  refine ⟨102886930791343186404836975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68591287194228790936557983 102886930791343186404836975)
  ·
    refine ⟨154330396187014779607255463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102886930791343186404836975 154330396187014779607255463)
    ·
      refine ⟨231495594280522169410883195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154330396187014779607255463 231495594280522169410883195)
      ·
        refine ⟨347243391420783254116324793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 231495594280522169410883195 347243391420783254116324793)
        ·
          refine ⟨260432543565587440587243595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 347243391420783254116324793 260432543565587440587243595)
          ·
            refine ⟨390648815348381160880865393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 260432543565587440587243595 390648815348381160880865393)
            ·
              refine ⟨292986611511285870660649045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 390648815348381160880865393 292986611511285870660649045)
              ·
                refine ⟨3433436853647881296804481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 292986611511285870660649045 3433436853647881296804481)
                ·
                  refine ⟨2575077640235910972603361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3433436853647881296804481 2575077640235910972603361)
                  ·
                    refine ⟨1931308230176933229452521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2575077640235910972603361 1931308230176933229452521)
                    ·
                      refine ⟨1448481172632699922089391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1931308230176933229452521 1448481172632699922089391)
                      ·
                        rfl

theorem cell23_2820907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 8, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 8, 2, 2, 2].length) (baseStart_2820907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2820907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2820907 prefixEnd_2820907 := by exact prefixLift 2820907
  have htrace : WordTrace (prefixWord ++ tailWord_2820907) baseStart_2820907 baseEnd_2820907 := by
    simpa [prefixWord, tailWord_2820907, baseEnd_2820907] using wordTrace_append hprefix tailTrace_2820907
  have hstable : (prefixWord ++ tailWord_2820907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2820907).length < 2 ^ (prefixWord ++ tailWord_2820907).sum := by decide
  have hdescent : baseEnd_2820907 < baseStart_2820907 := by decide
  rcases family_descends (prefixWord ++ tailWord_2820907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2820913 : List Nat := [1, 2, 2, 3, 2, 1, 2, 3, 7]
def baseStart_2820913 : Nat := 118140960795 + 2820913 * 2 ^ 59
def prefixEnd_2820913 : Nat := 4983230072969 + 3 ^ 40 * 2820913 * 2
def baseEnd_2820913 : Nat := 160942694835180766512707

theorem tailTrace_2820913 : CollatzResearch.WordTrace tailWord_2820913 prefixEnd_2820913 160942694835180766512707 := by
  unfold tailWord_2820913
  simp only [CollatzResearch.WordTrace]
  refine ⟨102887149629321449429555393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68591433086214299619703595 102887149629321449429555393)
  ·
    refine ⟨77165362221991087072166545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102887149629321449429555393 77165362221991087072166545)
    ·
      refine ⟨57874021666493315304124909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77165362221991087072166545 57874021666493315304124909)
      ·
        refine ⟨21702758124934993239046841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57874021666493315304124909 21702758124934993239046841)
        ·
          refine ⟨16277068593701244929285131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21702758124934993239046841 16277068593701244929285131)
          ·
            refine ⟨24415602890551867393927697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16277068593701244929285131 24415602890551867393927697)
            ·
              refine ⟨18311702167913900545445773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24415602890551867393927697 18311702167913900545445773)
              ·
                refine ⟨6866888312967712704542165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18311702167913900545445773 6866888312967712704542165)
                ·
                  refine ⟨160942694835180766512707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6866888312967712704542165 160942694835180766512707)
                  ·
                    rfl

theorem cell23_2820913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 3, 7].length) (baseStart_2820913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2820913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2820913 prefixEnd_2820913 := by exact prefixLift 2820913
  have htrace : WordTrace (prefixWord ++ tailWord_2820913) baseStart_2820913 baseEnd_2820913 := by
    simpa [prefixWord, tailWord_2820913, baseEnd_2820913] using wordTrace_append hprefix tailTrace_2820913
  have hstable : (prefixWord ++ tailWord_2820913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2820913).length < 2 ^ (prefixWord ++ tailWord_2820913).sum := by decide
  have hdescent : baseEnd_2820913 < baseStart_2820913 := by decide
  rcases family_descends (prefixWord ++ tailWord_2820913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2821003 : List Nat := [1, 1, 1, 1, 4, 2, 3, 2, 8]
def baseStart_2821003 : Nat := 118140960795 + 2821003 * 2 ^ 59
def prefixEnd_2821003 : Nat := 4983230072969 + 3 ^ 40 * 2821003 * 2
def baseEnd_2821003 : Nat := 160947829641725727387661

theorem tailTrace_2821003 : CollatzResearch.WordTrace tailWord_2821003 prefixEnd_2821003 160947829641725727387661 := by
  unfold tailWord_2821003
  simp only [CollatzResearch.WordTrace]
  refine ⟨102890432198995394800331663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68593621465996929866887775 102890432198995394800331663)
  ·
    refine ⟨154335648298493092200497495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102890432198995394800331663 154335648298493092200497495)
    ·
      refine ⟨231503472447739638300746243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154335648298493092200497495 231503472447739638300746243)
      ·
        refine ⟨347255208671609457451119365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 231503472447739638300746243 347255208671609457451119365)
        ·
          refine ⟨65110351625926773272084881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 347255208671609457451119365 65110351625926773272084881)
          ·
            refine ⟨48832763719445079954063661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65110351625926773272084881 48832763719445079954063661)
            ·
              refine ⟨18312286394791904982773873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48832763719445079954063661 18312286394791904982773873)
              ·
                refine ⟨13734214796093928737080405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18312286394791904982773873 13734214796093928737080405)
                ·
                  refine ⟨160947829641725727387661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 13734214796093928737080405 160947829641725727387661)
                  ·
                    rfl

theorem cell23_2821003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 2, 8].length) (baseStart_2821003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2821003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2821003 prefixEnd_2821003 := by exact prefixLift 2821003
  have htrace : WordTrace (prefixWord ++ tailWord_2821003) baseStart_2821003 baseEnd_2821003 := by
    simpa [prefixWord, tailWord_2821003, baseEnd_2821003] using wordTrace_append hprefix tailTrace_2821003
  have hstable : (prefixWord ++ tailWord_2821003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2821003).length < 2 ^ (prefixWord ++ tailWord_2821003).sum := by decide
  have hdescent : baseEnd_2821003 < baseStart_2821003 := by decide
  rcases family_descends (prefixWord ++ tailWord_2821003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2821043 : List Nat := [1, 1, 1, 2, 3, 1, 2, 1, 1, 3, 7]
def baseStart_2821043 : Nat := 118140960795 + 2821043 * 2 ^ 59
def prefixEnd_2821043 : Nat := 4983230072969 + 3 ^ 40 * 2821043 * 2
def baseEnd_2821043 : Nat := 1448551006001711389988765

theorem tailTrace_2821043 : CollatzResearch.WordTrace tailWord_2821043 prefixEnd_2821043 1448551006001711389988765 := by
  unfold tailWord_2821043
  simp only [CollatzResearch.WordTrace]
  refine ⟨102891891118850481631787783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68594594079233654421191855 102891891118850481631787783)
  ·
    refine ⟨154337836678275722447681675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102891891118850481631787783 154337836678275722447681675)
    ·
      refine ⟨231506755017413583671522513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154337836678275722447681675 231506755017413583671522513)
      ·
        refine ⟨173630066263060187753641885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 231506755017413583671522513 173630066263060187753641885)
        ·
          refine ⟨65111274848647570407615707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 173630066263060187753641885 65111274848647570407615707)
          ·
            refine ⟨97666912272971355611423561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65111274848647570407615707 97666912272971355611423561)
            ·
              refine ⟨73250184204728516708567671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97666912272971355611423561 73250184204728516708567671)
              ·
                refine ⟨109875276307092775062851507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73250184204728516708567671 109875276307092775062851507)
                ·
                  refine ⟨164812914460639162594277261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 109875276307092775062851507 164812914460639162594277261)
                  ·
                    refine ⟨61804842922739685972853973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 164812914460639162594277261 61804842922739685972853973)
                    ·
                      refine ⟨1448551006001711389988765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 61804842922739685972853973 1448551006001711389988765)
                      ·
                        rfl

theorem cell23_2821043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 1, 1, 3, 7].length) (baseStart_2821043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2821043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2821043 prefixEnd_2821043 := by exact prefixLift 2821043
  have htrace : WordTrace (prefixWord ++ tailWord_2821043) baseStart_2821043 baseEnd_2821043 := by
    simpa [prefixWord, tailWord_2821043, baseEnd_2821043] using wordTrace_append hprefix tailTrace_2821043
  have hstable : (prefixWord ++ tailWord_2821043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2821043).length < 2 ^ (prefixWord ++ tailWord_2821043).sum := by decide
  have hdescent : baseEnd_2821043 < baseStart_2821043 := by decide
  rcases family_descends (prefixWord ++ tailWord_2821043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2821047 : List Nat := [1, 1, 3, 1, 3, 1, 2, 4, 3, 1, 3]
def baseStart_2821047 : Nat := 118140960795 + 2821047 * 2 ^ 59
def prefixEnd_2821047 : Nat := 4983230072969 + 3 ^ 40 * 2821047 * 2
def baseEnd_2821047 : Nat := 1448553059924329374338747

theorem tailTrace_2821047 : CollatzResearch.WordTrace tailWord_2821047 prefixEnd_2821047 1448553059924329374338747 := by
  unfold tailWord_2821047
  simp only [CollatzResearch.WordTrace]
  refine ⟨102892037010835990314933395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68594691340557326876622263 102892037010835990314933395)
  ·
    refine ⟨154338055516253985472400093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102892037010835990314933395 154338055516253985472400093)
    ·
      refine ⟨57876770818595244552150035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 154338055516253985472400093 57876770818595244552150035)
      ·
        refine ⟨86815156227892866828225053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57876770818595244552150035 86815156227892866828225053)
        ·
          refine ⟨32555683585459825060584395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86815156227892866828225053 32555683585459825060584395)
          ·
            refine ⟨48833525378189737590876593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32555683585459825060584395 48833525378189737590876593)
            ·
              refine ⟨36625144033642303193157445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48833525378189737590876593 36625144033642303193157445)
              ·
                refine ⟨6867214506307931848717021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36625144033642303193157445 6867214506307931848717021)
                ·
                  refine ⟨2575205439865474443268883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6867214506307931848717021 2575205439865474443268883)
                  ·
                    refine ⟨3862808159798211664903325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2575205439865474443268883 3862808159798211664903325)
                    ·
                      refine ⟨1448553059924329374338747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3862808159798211664903325 1448553059924329374338747)
                      ·
                        rfl

theorem cell23_2821047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 4, 3, 1, 3].length) (baseStart_2821047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2821047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2821047 prefixEnd_2821047 := by exact prefixLift 2821047
  have htrace : WordTrace (prefixWord ++ tailWord_2821047) baseStart_2821047 baseEnd_2821047 := by
    simpa [prefixWord, tailWord_2821047, baseEnd_2821047] using wordTrace_append hprefix tailTrace_2821047
  have hstable : (prefixWord ++ tailWord_2821047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2821047).length < 2 ^ (prefixWord ++ tailWord_2821047).sum := by decide
  have hdescent : baseEnd_2821047 < baseStart_2821047 := by decide
  rcases family_descends (prefixWord ++ tailWord_2821047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2821050 : List Nat := [3, 1, 1, 1, 2, 1, 5, 1, 3, 5]
def baseStart_2821050 : Nat := 118140960795 + 2821050 * 2 ^ 59
def prefixEnd_2821050 : Nat := 4983230072969 + 3 ^ 40 * 2821050 * 2
def baseEnd_2821050 : Nat := 482851533455430954200411

theorem tailTrace_2821050 : CollatzResearch.WordTrace tailWord_2821050 prefixEnd_2821050 482851533455430954200411 := by
  unfold tailWord_2821050
  simp only [CollatzResearch.WordTrace]
  refine ⟨25723036607456280456823151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68594764286550081218195069 25723036607456280456823151)
  ·
    refine ⟨38584554911184420685234727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25723036607456280456823151 38584554911184420685234727)
    ·
      refine ⟨57876832366776631027852091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38584554911184420685234727 57876832366776631027852091)
      ·
        refine ⟨86815248550164946541778137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57876832366776631027852091 86815248550164946541778137)
        ·
          refine ⟨65111436412623709906333603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86815248550164946541778137 65111436412623709906333603)
          ·
            refine ⟨97667154618935564859500405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65111436412623709906333603 97667154618935564859500405)
            ·
              refine ⟨9156295745525209205578163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 97667154618935564859500405 9156295745525209205578163)
              ·
                refine ⟨13734443618287813808367245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9156295745525209205578163 13734443618287813808367245)
                ·
                  refine ⟨5150416356857930178137717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13734443618287813808367245 5150416356857930178137717)
                  ·
                    refine ⟨482851533455430954200411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5150416356857930178137717 482851533455430954200411)
                    ·
                      rfl

theorem cell23_2821050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 5, 1, 3, 5].length) (baseStart_2821050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2821050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2821050 prefixEnd_2821050 := by exact prefixLift 2821050
  have htrace : WordTrace (prefixWord ++ tailWord_2821050) baseStart_2821050 baseEnd_2821050 := by
    simpa [prefixWord, tailWord_2821050, baseEnd_2821050] using wordTrace_append hprefix tailTrace_2821050
  have hstable : (prefixWord ++ tailWord_2821050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2821050).length < 2 ^ (prefixWord ++ tailWord_2821050).sum := by decide
  have hdescent : baseEnd_2821050 < baseStart_2821050 := by decide
  rcases family_descends (prefixWord ++ tailWord_2821050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2821081 : List Nat := [1, 2, 1, 2, 5, 2, 1, 4, 1, 1, 3]
def baseStart_2821081 : Nat := 118140960795 + 2821081 * 2 ^ 59
def prefixEnd_2821081 : Nat := 4983230072969 + 3 ^ 40 * 2821081 * 2
def baseEnd_2821081 : Nat := 1448570518266582241313591

theorem tailTrace_2821081 : CollatzResearch.WordTrace tailWord_2821081 prefixEnd_2821081 1448570518266582241313591 := by
  unfold tailWord_2821081
  simp only [CollatzResearch.WordTrace]
  refine ⟨102893277092712814121671097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68595518061808542747780731 102893277092712814121671097)
  ·
    refine ⟨77169957819534610591253323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102893277092712814121671097 77169957819534610591253323)
    ·
      refine ⟨115754936729301915886879985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77169957819534610591253323 115754936729301915886879985)
      ·
        refine ⟨86816202546976436915159989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115754936729301915886879985 86816202546976436915159989)
        ·
          refine ⟨8139018988779040960796249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 86816202546976436915159989 8139018988779040960796249)
          ·
            refine ⟨6104264241584280720597187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8139018988779040960796249 6104264241584280720597187)
            ·
              refine ⟨9156396362376421080895781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6104264241584280720597187 9156396362376421080895781)
              ·
                refine ⟨1716824317945578952667959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9156396362376421080895781 1716824317945578952667959)
                ·
                  refine ⟨2575236476918368429001939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1716824317945578952667959 2575236476918368429001939)
                  ·
                    refine ⟨3862854715377552643502909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2575236476918368429001939 3862854715377552643502909)
                    ·
                      refine ⟨1448570518266582241313591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3862854715377552643502909 1448570518266582241313591)
                      ·
                        rfl

theorem cell23_2821081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 1, 4, 1, 1, 3].length) (baseStart_2821081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2821081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2821081 prefixEnd_2821081 := by exact prefixLift 2821081
  have htrace : WordTrace (prefixWord ++ tailWord_2821081) baseStart_2821081 baseEnd_2821081 := by
    simpa [prefixWord, tailWord_2821081, baseEnd_2821081] using wordTrace_append hprefix tailTrace_2821081
  have hstable : (prefixWord ++ tailWord_2821081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2821081).length < 2 ^ (prefixWord ++ tailWord_2821081).sum := by decide
  have hdescent : baseEnd_2821081 < baseStart_2821081 := by decide
  rcases family_descends (prefixWord ++ tailWord_2821081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
