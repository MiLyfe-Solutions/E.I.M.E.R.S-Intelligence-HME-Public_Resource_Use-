import V185TrunkScan20Chunk140

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_857501 : List Nat := [1, 4, 2, 1, 3, 1, 2, 3, 3]
def baseStart_857501 : Nat := 118140960795 + 857501 * 2 ^ 59
def prefixEnd_857501 : Nat := 4983230072969 + 3 ^ 40 * 857501 * 2
def baseEnd_857501 : Nat := 391386821965470895194605

theorem tailTrace_857501 : CollatzResearch.WordTrace tailWord_857501 prefixEnd_857501 391386821965470895194605 := by
  unfold tailWord_857501
  simp only [CollatzResearch.WordTrace]
  refine ⟨31275630866427801356468357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20850420577618534237645571 31275630866427801356468357)
  ·
    refine ⟨5864180787455212754337817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31275630866427801356468357 5864180787455212754337817)
    ·
      refine ⟨4398135590591409565753363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5864180787455212754337817 4398135590591409565753363)
      ·
        refine ⟨6597203385887114348630045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4398135590591409565753363 6597203385887114348630045)
        ·
          refine ⟨2473951269707667880736267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6597203385887114348630045 2473951269707667880736267)
          ·
            refine ⟨3710926904561501821104401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2473951269707667880736267 3710926904561501821104401)
            ·
              refine ⟨2783195178421126365828301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3710926904561501821104401 2783195178421126365828301)
              ·
                refine ⟨1043698191907922387185613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2783195178421126365828301 1043698191907922387185613)
                ·
                  refine ⟨391386821965470895194605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1043698191907922387185613 391386821965470895194605)
                  ·
                    rfl

theorem cell20_857501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 2, 3, 3].length) (baseStart_857501 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_857501 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_857501 prefixEnd_857501 := by exact prefixLift 857501
  have htrace : WordTrace (prefixWord ++ tailWord_857501) baseStart_857501 baseEnd_857501 := by
    simpa [prefixWord, tailWord_857501, baseEnd_857501] using wordTrace_append hprefix tailTrace_857501
  have hstable : (prefixWord ++ tailWord_857501).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_857501).length < 2 ^ (prefixWord ++ tailWord_857501).sum := by decide
  have hdescent : baseEnd_857501 < baseStart_857501 := by decide
  rcases family_descends (prefixWord ++ tailWord_857501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_857525 : List Nat := [1, 3, 3, 2, 2, 1, 1, 5, 2]
def baseStart_857525 : Nat := 118140960795 + 857525 * 2 ^ 59
def prefixEnd_857525 : Nat := 4983230072969 + 3 ^ 40 * 857525 * 2
def baseEnd_857525 : Nat := 391397776219433478394507

theorem tailTrace_857525 : CollatzResearch.WordTrace tailWord_857525 prefixEnd_857525 391397776219433478394507 := by
  unfold tailWord_857525
  simp only [CollatzResearch.WordTrace]
  refine ⟨31276506218340853455342029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20851004145560568970228019 31276506218340853455342029)
  ·
    refine ⟨11728689831877820045753261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31276506218340853455342029 11728689831877820045753261)
    ·
      refine ⟨4398258686954182517157473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11728689831877820045753261 4398258686954182517157473)
      ·
        refine ⟨3298694015215636887868105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4398258686954182517157473 3298694015215636887868105)
        ·
          refine ⟨2474020511411727665901079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3298694015215636887868105 2474020511411727665901079)
          ·
            refine ⟨3711030767117591498851619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2474020511411727665901079 3711030767117591498851619)
            ·
              refine ⟨5566546150676387248277429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3711030767117591498851619 5566546150676387248277429)
              ·
                refine ⟨521863701625911304526009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5566546150676387248277429 521863701625911304526009)
                ·
                  refine ⟨391397776219433478394507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 521863701625911304526009 391397776219433478394507)
                  ·
                    rfl

theorem cell20_857525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 5, 2].length) (baseStart_857525 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_857525 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_857525 prefixEnd_857525 := by exact prefixLift 857525
  have htrace : WordTrace (prefixWord ++ tailWord_857525) baseStart_857525 baseEnd_857525 := by
    simpa [prefixWord, tailWord_857525, baseEnd_857525] using wordTrace_append hprefix tailTrace_857525
  have hstable : (prefixWord ++ tailWord_857525).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_857525).length < 2 ^ (prefixWord ++ tailWord_857525).sum := by decide
  have hdescent : baseEnd_857525 < baseStart_857525 := by decide
  rcases family_descends (prefixWord ++ tailWord_857525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_857538 : List Nat := [3, 5, 2, 1, 1, 1, 2, 1, 4]
def baseStart_857538 : Nat := 118140960795 + 857538 * 2 ^ 59
def prefixEnd_857538 : Nat := 4983230072969 + 3 ^ 40 * 857538 * 2
def baseEnd_857538 : Nat := 391403709773663210961121

theorem tailTrace_857538 : CollatzResearch.WordTrace tailWord_857538 prefixEnd_857538 391403709773663210961121 := by
  unfold tailWord_857538
  simp only [CollatzResearch.WordTrace]
  refine ⟨7819245091823439168891317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20851320244862504450376845 7819245091823439168891317)
  ·
    refine ⟨733054227358447422083561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7819245091823439168891317 733054227358447422083561)
    ·
      refine ⟨549790670518835566562671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 733054227358447422083561 549790670518835566562671)
      ·
        refine ⟨824686005778253349844007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 549790670518835566562671 824686005778253349844007)
        ·
          refine ⟨1237029008667380024766011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 824686005778253349844007 1237029008667380024766011)
          ·
            refine ⟨1855543513001070037149017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1237029008667380024766011 1855543513001070037149017)
            ·
              refine ⟨1391657634750802527861763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1855543513001070037149017 1391657634750802527861763)
              ·
                refine ⟨2087486452126203791792645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1391657634750802527861763 2087486452126203791792645)
                ·
                  refine ⟨391403709773663210961121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2087486452126203791792645 391403709773663210961121)
                  ·
                    rfl

theorem cell20_857538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 2, 1, 4].length) (baseStart_857538 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_857538 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_857538 prefixEnd_857538 := by exact prefixLift 857538
  have htrace : WordTrace (prefixWord ++ tailWord_857538) baseStart_857538 baseEnd_857538 := by
    simpa [prefixWord, tailWord_857538, baseEnd_857538] using wordTrace_append hprefix tailTrace_857538
  have hstable : (prefixWord ++ tailWord_857538).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_857538).length < 2 ^ (prefixWord ++ tailWord_857538).sum := by decide
  have hdescent : baseEnd_857538 < baseStart_857538 := by decide
  rcases family_descends (prefixWord ++ tailWord_857538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_857546 : List Nat := [3, 1, 2, 1, 2, 4, 2, 1, 4]
def baseStart_857546 : Nat := 118140960795 + 857546 * 2 ^ 59
def prefixEnd_857546 : Nat := 4983230072969 + 3 ^ 40 * 857546 * 2
def baseEnd_857546 : Nat := 391407361191650738694421

theorem tailTrace_857546 : CollatzResearch.WordTrace tailWord_857546 prefixEnd_857546 391407361191650738694421 := by
  unfold tailWord_857546
  simp only [CollatzResearch.WordTrace]
  refine ⟨7819318037816193510464123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20851514767509849361237661 7819318037816193510464123)
  ·
    refine ⟨11728977056724290265696185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7819318037816193510464123 11728977056724290265696185)
    ·
      refine ⟨8796732792543217699272139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11728977056724290265696185 8796732792543217699272139)
      ·
        refine ⟨13195099188814826548908209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8796732792543217699272139 13195099188814826548908209)
        ·
          refine ⟨9896324391611119911681157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13195099188814826548908209 9896324391611119911681157)
          ·
            refine ⟨1855560823427084983440217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9896324391611119911681157 1855560823427084983440217)
            ·
              refine ⟨1391670617570313737580163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1855560823427084983440217 1391670617570313737580163)
              ·
                refine ⟨2087505926355470606370245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1391670617570313737580163 2087505926355470606370245)
                ·
                  refine ⟨391407361191650738694421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2087505926355470606370245 391407361191650738694421)
                  ·
                    rfl

theorem cell20_857546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 2, 1, 4].length) (baseStart_857546 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_857546 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_857546 prefixEnd_857546 := by exact prefixLift 857546
  have htrace : WordTrace (prefixWord ++ tailWord_857546) baseStart_857546 baseEnd_857546 := by
    simpa [prefixWord, tailWord_857546, baseEnd_857546] using wordTrace_append hprefix tailTrace_857546
  have hstable : (prefixWord ++ tailWord_857546).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_857546).length < 2 ^ (prefixWord ++ tailWord_857546).sum := by decide
  have hdescent : baseEnd_857546 < baseStart_857546 := by decide
  rcases family_descends (prefixWord ++ tailWord_857546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_857560 : List Nat := [2, 1, 2, 2, 2, 1, 2, 5, 3]
def baseStart_857560 : Nat := 118140960795 + 857560 * 2 ^ 59
def prefixEnd_857560 : Nat := 4983230072969 + 3 ^ 40 * 857560 * 2
def baseEnd_857560 : Nat := 391413751173128912227697

theorem tailTrace_857560 : CollatzResearch.WordTrace tailWord_857560 prefixEnd_857560 391413751173128912227697 := by
  unfold tailWord_857560
  simp only [CollatzResearch.WordTrace]
  refine ⟨15638891386607027216433067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20851855182142702955244089 15638891386607027216433067)
  ·
    refine ⟨23458337079910540824649601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15638891386607027216433067 23458337079910540824649601)
    ·
      refine ⟨17593752809932905618487201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23458337079910540824649601 17593752809932905618487201)
      ·
        refine ⟨13195314607449679213865401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17593752809932905618487201 13195314607449679213865401)
        ·
          refine ⟨9896485955587259410399051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13195314607449679213865401 9896485955587259410399051)
          ·
            refine ⟨14844728933380889115598577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9896485955587259410399051 14844728933380889115598577)
            ·
              refine ⟨11133546700035666836698933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14844728933380889115598577 11133546700035666836698933)
              ·
                refine ⟨1043770003128343765940525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11133546700035666836698933 1043770003128343765940525)
                ·
                  refine ⟨391413751173128912227697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1043770003128343765940525 391413751173128912227697)
                  ·
                    rfl

theorem cell20_857560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 5, 3].length) (baseStart_857560 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_857560 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_857560 prefixEnd_857560 := by exact prefixLift 857560
  have htrace : WordTrace (prefixWord ++ tailWord_857560) baseStart_857560 baseEnd_857560 := by
    simpa [prefixWord, tailWord_857560, baseEnd_857560] using wordTrace_append hprefix tailTrace_857560
  have hstable : (prefixWord ++ tailWord_857560).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_857560).length < 2 ^ (prefixWord ++ tailWord_857560).sum := by decide
  have hdescent : baseEnd_857560 < baseStart_857560 := by decide
  rcases family_descends (prefixWord ++ tailWord_857560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_857567 : List Nat := [1, 1, 2, 3, 3, 1, 1, 4, 4]
def baseStart_857567 : Nat := 118140960795 + 857567 * 2 ^ 59
def prefixEnd_857567 : Nat := 4983230072969 + 3 ^ 40 * 857567 * 2
def baseEnd_857567 : Nat := 391416946163867998994335

theorem tailTrace_857567 : CollatzResearch.WordTrace tailWord_857567 prefixEnd_857567 391416946163867998994335 := by
  unfold tailWord_857567
  simp only [CollatzResearch.WordTrace]
  refine ⟨31278038084188694628370955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20852025389459129752247303 31278038084188694628370955)
  ·
    refine ⟨46917057126283041942556433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31278038084188694628370955 46917057126283041942556433)
    ·
      refine ⟨35187792844712281456917325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46917057126283041942556433 35187792844712281456917325)
      ·
        refine ⟨13195422316767105546343997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35187792844712281456917325 13195422316767105546343997)
        ·
          refine ⟨4948283368787664579878999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13195422316767105546343997 4948283368787664579878999)
          ·
            refine ⟨7422425053181496869818499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4948283368787664579878999 7422425053181496869818499)
            ·
              refine ⟨11133637579772245304727749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7422425053181496869818499 11133637579772245304727749)
              ·
                refine ⟨2087557046207295994636453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11133637579772245304727749 2087557046207295994636453)
                ·
                  refine ⟨391416946163867998994335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2087557046207295994636453 391416946163867998994335)
                  ·
                    rfl

theorem cell20_857567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 4, 4].length) (baseStart_857567 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_857567 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_857567 prefixEnd_857567 := by exact prefixLift 857567
  have htrace : WordTrace (prefixWord ++ tailWord_857567) baseStart_857567 baseEnd_857567 := by
    simpa [prefixWord, tailWord_857567, baseEnd_857567] using wordTrace_append hprefix tailTrace_857567
  have hstable : (prefixWord ++ tailWord_857567).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_857567).length < 2 ^ (prefixWord ++ tailWord_857567).sum := by decide
  have hdescent : baseEnd_857567 < baseStart_857567 := by decide
  rcases family_descends (prefixWord ++ tailWord_857567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_857601 : List Nat := [1, 2, 4, 1, 4, 2, 1, 1, 4]
def baseStart_857601 : Nat := 118140960795 + 857601 * 2 ^ 59
def prefixEnd_857601 : Nat := 4983230072969 + 3 ^ 40 * 857601 * 2
def baseEnd_857601 : Nat := 391432464690314991860863

theorem tailTrace_857601 : CollatzResearch.WordTrace tailWord_857601 prefixEnd_857601 391432464690314991860863 := by
  unfold tailWord_857601
  simp only [CollatzResearch.WordTrace]
  refine ⟨31279278166065518435108657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20852852110710345623405771 31279278166065518435108657)
  ·
    refine ⟨23459458624549138826331493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31279278166065518435108657 23459458624549138826331493)
    ·
      refine ⟨4398648492102963529937155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23459458624549138826331493 4398648492102963529937155)
      ·
        refine ⟨6597972738154445294905733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4398648492102963529937155 6597972738154445294905733)
        ·
          refine ⟨1237119888403958492794825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6597972738154445294905733 1237119888403958492794825)
          ·
            refine ⟨927839916302968869596119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1237119888403958492794825 927839916302968869596119)
            ·
              refine ⟨1391759874454453304394179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 927839916302968869596119 1391759874454453304394179)
              ·
                refine ⟨2087639811681679956591269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1391759874454453304394179 2087639811681679956591269)
                ·
                  refine ⟨391432464690314991860863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2087639811681679956591269 391432464690314991860863)
                  ·
                    rfl

theorem cell20_857601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 1, 1, 4].length) (baseStart_857601 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_857601 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_857601 prefixEnd_857601 := by exact prefixLift 857601
  have htrace : WordTrace (prefixWord ++ tailWord_857601) baseStart_857601 baseEnd_857601 := by
    simpa [prefixWord, tailWord_857601, baseEnd_857601] using wordTrace_append hprefix tailTrace_857601
  have hstable : (prefixWord ++ tailWord_857601).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_857601).length < 2 ^ (prefixWord ++ tailWord_857601).sum := by decide
  have hdescent : baseEnd_857601 < baseStart_857601 := by decide
  rcases family_descends (prefixWord ++ tailWord_857601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_857611 : List Nat := [1, 1, 1, 1, 9, 1, 2, 1, 3]
def baseStart_857611 : Nat := 118140960795 + 857611 * 2 ^ 59
def prefixEnd_857611 : Nat := 4983230072969 + 3 ^ 40 * 857611 * 2
def baseEnd_857611 : Nat := 391437028962799401527489

theorem tailTrace_857611 : CollatzResearch.WordTrace tailWord_857611 prefixEnd_857611 391437028962799401527489 := by
  unfold tailWord_857611
  simp only [CollatzResearch.WordTrace]
  refine ⟨31279642896029290142972687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20853095264019526761981791 31279642896029290142972687)
  ·
    refine ⟨46919464344043935214459031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31279642896029290142972687 46919464344043935214459031)
    ·
      refine ⟨70379196516065902821688547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46919464344043935214459031 70379196516065902821688547)
      ·
        refine ⟨105568794774098854232532821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70379196516065902821688547 105568794774098854232532821)
        ·
          refine ⟨618567156879485474018747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 105568794774098854232532821 618567156879485474018747)
          ·
            refine ⟨927850735319228211028121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 618567156879485474018747 927850735319228211028121)
            ·
              refine ⟨695888051489421158271091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 927850735319228211028121 695888051489421158271091)
              ·
                refine ⟨1043832077234131737406637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 695888051489421158271091 1043832077234131737406637)
                ·
                  refine ⟨391437028962799401527489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1043832077234131737406637 391437028962799401527489)
                  ·
                    rfl

theorem cell20_857611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 2, 1, 3].length) (baseStart_857611 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_857611 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_857611 prefixEnd_857611 := by exact prefixLift 857611
  have htrace : WordTrace (prefixWord ++ tailWord_857611) baseStart_857611 baseEnd_857611 := by
    simpa [prefixWord, tailWord_857611, baseEnd_857611] using wordTrace_append hprefix tailTrace_857611
  have hstable : (prefixWord ++ tailWord_857611).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_857611).length < 2 ^ (prefixWord ++ tailWord_857611).sum := by decide
  have hdescent : baseEnd_857611 < baseStart_857611 := by decide
  rcases family_descends (prefixWord ++ tailWord_857611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_857653 : List Nat := [1, 3, 3, 1, 1, 4, 2, 2, 3]
def baseStart_857653 : Nat := 118140960795 + 857653 * 2 ^ 59
def prefixEnd_857653 : Nat := 4983230072969 + 3 ^ 40 * 857653 * 2
def baseEnd_857653 : Nat := 391456198907233922127317

theorem tailTrace_857653 : CollatzResearch.WordTrace tailWord_857653 prefixEnd_857653 391456198907233922127317 := by
  unfold tailWord_857653
  simp only [CollatzResearch.WordTrace]
  refine ⟨31281174761877131316001613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20854116507918087544001075 31281174761877131316001613)
  ·
    refine ⟨11730440535703924243500605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31281174761877131316001613 11730440535703924243500605)
    ·
      refine ⟨4398915200888971591312727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11730440535703924243500605 4398915200888971591312727)
      ·
        refine ⟨6598372801333457386969091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4398915200888971591312727 6598372801333457386969091)
        ·
          refine ⟨9897559202000186080453637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6598372801333457386969091 9897559202000186080453637)
          ·
            refine ⟨1855792350375034890085057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9897559202000186080453637 1855792350375034890085057)
            ·
              refine ⟨1391844262781276167563793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1855792350375034890085057 1391844262781276167563793)
              ·
                refine ⟨1043883197085957125672845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1391844262781276167563793 1043883197085957125672845)
                ·
                  refine ⟨391456198907233922127317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1043883197085957125672845 391456198907233922127317)
                  ·
                    rfl

theorem cell20_857653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 2, 2, 3].length) (baseStart_857653 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_857653 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_857653 prefixEnd_857653 := by exact prefixLift 857653
  have htrace : WordTrace (prefixWord ++ tailWord_857653) baseStart_857653 baseEnd_857653 := by
    simpa [prefixWord, tailWord_857653, baseEnd_857653] using wordTrace_append hprefix tailTrace_857653
  have hstable : (prefixWord ++ tailWord_857653).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_857653).length < 2 ^ (prefixWord ++ tailWord_857653).sum := by decide
  have hdescent : baseEnd_857653 < baseStart_857653 := by decide
  rcases family_descends (prefixWord ++ tailWord_857653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_857656 : List Nat := [2, 1, 2, 1, 4, 4, 2, 2, 2]
def baseStart_857656 : Nat := 118140960795 + 857656 * 2 ^ 59
def prefixEnd_857656 : Nat := 4983230072969 + 3 ^ 40 * 857656 * 2
def baseEnd_857656 : Nat := 391457568188979245027305

theorem tailTrace_857656 : CollatzResearch.WordTrace tailWord_857656 prefixEnd_857656 391457568188979245027305 := by
  unfold tailWord_857656
  simp only [CollatzResearch.WordTrace]
  refine ⟨15640642090433131414180411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20854189453910841885573881 15640642090433131414180411)
  ·
    refine ⟨23460963135649697121270617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15640642090433131414180411 23460963135649697121270617)
    ·
      refine ⟨17595722351737272840952963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23460963135649697121270617 17595722351737272840952963)
      ·
        refine ⟨26393583527605909261429445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17595722351737272840952963 26393583527605909261429445)
        ·
          refine ⟨4948796911426107986518021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26393583527605909261429445 4948796911426107986518021)
          ·
            refine ⟨927899420892395247472129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4948796911426107986518021 927899420892395247472129)
            ·
              refine ⟨695924565669296435604097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 927899420892395247472129 695924565669296435604097)
              ·
                refine ⟨521943424251972326703073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 695924565669296435604097 521943424251972326703073)
                ·
                  refine ⟨391457568188979245027305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 521943424251972326703073 391457568188979245027305)
                  ·
                    rfl

theorem cell20_857656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 2, 2, 2].length) (baseStart_857656 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_857656 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_857656 prefixEnd_857656 := by exact prefixLift 857656
  have htrace : WordTrace (prefixWord ++ tailWord_857656) baseStart_857656 baseEnd_857656 := by
    simpa [prefixWord, tailWord_857656, baseEnd_857656] using wordTrace_append hprefix tailTrace_857656
  have hstable : (prefixWord ++ tailWord_857656).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_857656).length < 2 ^ (prefixWord ++ tailWord_857656).sum := by decide
  have hdescent : baseEnd_857656 < baseStart_857656 := by decide
  rcases family_descends (prefixWord ++ tailWord_857656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_857674 : List Nat := [3, 1, 2, 1, 1, 3, 1, 5, 3]
def baseStart_857674 : Nat := 118140960795 + 857674 * 2 ^ 59
def prefixEnd_857674 : Nat := 4983230072969 + 3 ^ 40 * 857674 * 2
def baseEnd_857674 : Nat := 391465783879451182427231

theorem tailTrace_857674 : CollatzResearch.WordTrace tailWord_857674 prefixEnd_857674 391465783879451182427231 := by
  unfold tailWord_857674
  simp only [CollatzResearch.WordTrace]
  refine ⟨7820485173700262975629019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20854627129867367935010717 7820485173700262975629019)
  ·
    refine ⟨11730727760550394463443529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7820485173700262975629019 11730727760550394463443529)
    ·
      refine ⟨8798045820412795847582647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11730727760550394463443529 8798045820412795847582647)
      ·
        refine ⟨13197068730619193771373971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8798045820412795847582647 13197068730619193771373971)
        ·
          refine ⟨19795603095928790657060957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13197068730619193771373971 19795603095928790657060957)
          ·
            refine ⟨7423351160973296496397859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19795603095928790657060957 7423351160973296496397859)
            ·
              refine ⟨11135026741459944744596789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7423351160973296496397859 11135026741459944744596789)
              ·
                refine ⟨1043908757011869819805949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11135026741459944744596789 1043908757011869819805949)
                ·
                  refine ⟨391465783879451182427231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1043908757011869819805949 391465783879451182427231)
                  ·
                    rfl

theorem cell20_857674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 5, 3].length) (baseStart_857674 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_857674 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_857674 prefixEnd_857674 := by exact prefixLift 857674
  have htrace : WordTrace (prefixWord ++ tailWord_857674) baseStart_857674 baseEnd_857674 := by
    simpa [prefixWord, tailWord_857674, baseEnd_857674] using wordTrace_append hprefix tailTrace_857674
  have hstable : (prefixWord ++ tailWord_857674).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_857674).length < 2 ^ (prefixWord ++ tailWord_857674).sum := by decide
  have hdescent : baseEnd_857674 < baseStart_857674 := by decide
  rcases family_descends (prefixWord ++ tailWord_857674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_857677 : List Nat := [1, 6, 1, 1, 3, 1, 1, 2, 4]
def baseStart_857677 : Nat := 118140960795 + 857677 * 2 ^ 59
def prefixEnd_857677 : Nat := 4983230072969 + 3 ^ 40 * 857677 * 2
def baseEnd_857677 : Nat := 391467153161196505327219

theorem tailTrace_857677 : CollatzResearch.WordTrace tailWord_857677 prefixEnd_857677 391467153161196505327219 := by
  unfold tailWord_857677
  simp only [CollatzResearch.WordTrace]
  refine ⟨31282050113790183414875285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20854700075860122276583523 31282050113790183414875285)
  ·
    refine ⟨1466346099083914847572279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 31282050113790183414875285 1466346099083914847572279)
    ·
      refine ⟨2199519148625872271358419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1466346099083914847572279 2199519148625872271358419)
      ·
        refine ⟨3299278722938808407037629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2199519148625872271358419 3299278722938808407037629)
        ·
          refine ⟨1237229521102053152639111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3299278722938808407037629 1237229521102053152639111)
          ·
            refine ⟨1855844281653079728958667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1237229521102053152639111 1855844281653079728958667)
            ·
              refine ⟨2783766422479619593438001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1855844281653079728958667 2783766422479619593438001)
              ·
                refine ⟨2087824816859714695078501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2783766422479619593438001 2087824816859714695078501)
                ·
                  refine ⟨391467153161196505327219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2087824816859714695078501 391467153161196505327219)
                  ·
                    rfl

theorem cell20_857677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 1, 2, 4].length) (baseStart_857677 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_857677 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_857677 prefixEnd_857677 := by exact prefixLift 857677
  have htrace : WordTrace (prefixWord ++ tailWord_857677) baseStart_857677 baseEnd_857677 := by
    simpa [prefixWord, tailWord_857677, baseEnd_857677] using wordTrace_append hprefix tailTrace_857677
  have hstable : (prefixWord ++ tailWord_857677).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_857677).length < 2 ^ (prefixWord ++ tailWord_857677).sum := by decide
  have hdescent : baseEnd_857677 < baseStart_857677 := by decide
  rcases family_descends (prefixWord ++ tailWord_857677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_857681 : List Nat := [1, 2, 2, 1, 3, 2, 3, 2, 4]
def baseStart_857681 : Nat := 118140960795 + 857681 * 2 ^ 59
def prefixEnd_857681 : Nat := 4983230072969 + 3 ^ 40 * 857681 * 2
def baseEnd_857681 : Nat := 391468978870190269193869

theorem tailTrace_857681 : CollatzResearch.WordTrace tailWord_857681 prefixEnd_857681 391468978870190269193869 := by
  unfold tailWord_857681
  simp only [CollatzResearch.WordTrace]
  refine ⟨31282196005775692098020897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20854797337183794732013931 31282196005775692098020897)
  ·
    refine ⟨23461647004331769073515673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31282196005775692098020897 23461647004331769073515673)
    ·
      refine ⟨17596235253248826805136755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23461647004331769073515673 17596235253248826805136755)
      ·
        refine ⟨26394352879873240207705133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17596235253248826805136755 26394352879873240207705133)
        ·
          refine ⟨9897882329952465077889425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26394352879873240207705133 9897882329952465077889425)
          ·
            refine ⟨7423411747464348808417069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9897882329952465077889425 7423411747464348808417069)
            ·
              refine ⟨2783779405299130803156401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7423411747464348808417069 2783779405299130803156401)
              ·
                refine ⟨2087834553974348102367301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2783779405299130803156401 2087834553974348102367301)
                ·
                  refine ⟨391468978870190269193869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2087834553974348102367301 391468978870190269193869)
                  ·
                    rfl

theorem cell20_857681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 3, 2, 4].length) (baseStart_857681 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_857681 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_857681 prefixEnd_857681 := by exact prefixLift 857681
  have htrace : WordTrace (prefixWord ++ tailWord_857681) baseStart_857681 baseEnd_857681 := by
    simpa [prefixWord, tailWord_857681, baseEnd_857681] using wordTrace_append hprefix tailTrace_857681
  have hstable : (prefixWord ++ tailWord_857681).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_857681).length < 2 ^ (prefixWord ++ tailWord_857681).sum := by decide
  have hdescent : baseEnd_857681 < baseStart_857681 := by decide
  rcases family_descends (prefixWord ++ tailWord_857681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_857712 : List Nat := [2, 1, 1, 1, 6, 2, 1, 1, 5]
def baseStart_857712 : Nat := 118140960795 + 857712 * 2 ^ 59
def prefixEnd_857712 : Nat := 4983230072969 + 3 ^ 40 * 857712 * 2
def baseEnd_857712 : Nat := 391483128114891939160409

theorem tailTrace_857712 : CollatzResearch.WordTrace tailWord_857712 prefixEnd_857712 391483128114891939160409 := by
  unfold tailWord_857712
  simp only [CollatzResearch.WordTrace]
  refine ⟨15641663334331692196199695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20855551112442256261599593 15641663334331692196199695)
  ·
    refine ⟨23462495001497538294299543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15641663334331692196199695 23462495001497538294299543)
    ·
      refine ⟨35193742502246307441449315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23462495001497538294299543 35193742502246307441449315)
      ·
        refine ⟨52790613753369461162173973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35193742502246307441449315 52790613753369461162173973)
        ·
          refine ⟨2474560019689193491976905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 52790613753369461162173973 2474560019689193491976905)
          ·
            refine ⟨1855920014766895118982679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2474560019689193491976905 1855920014766895118982679)
            ·
              refine ⟨2783880022150342678474019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1855920014766895118982679 2783880022150342678474019)
              ·
                refine ⟨4175820033225514017711029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2783880022150342678474019 4175820033225514017711029)
                ·
                  refine ⟨391483128114891939160409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4175820033225514017711029 391483128114891939160409)
                  ·
                    rfl

theorem cell20_857712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 1, 1, 5].length) (baseStart_857712 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_857712 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_857712 prefixEnd_857712 := by exact prefixLift 857712
  have htrace : WordTrace (prefixWord ++ tailWord_857712) baseStart_857712 baseEnd_857712 := by
    simpa [prefixWord, tailWord_857712, baseEnd_857712] using wordTrace_append hprefix tailTrace_857712
  have hstable : (prefixWord ++ tailWord_857712).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_857712).length < 2 ^ (prefixWord ++ tailWord_857712).sum := by decide
  have hdescent : baseEnd_857712 < baseStart_857712 := by decide
  rcases family_descends (prefixWord ++ tailWord_857712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_857764 : List Nat := [2, 3, 1, 2, 2, 2, 8]
def baseStart_857764 : Nat := 118140960795 + 857764 * 2 ^ 59
def prefixEnd_857764 : Nat := 4983230072969 + 3 ^ 40 * 857764 * 2
def baseEnd_857764 : Nat := 43500762481312318825207

theorem tailTrace_857764 : CollatzResearch.WordTrace tailWord_857764 prefixEnd_857764 43500762481312318825207 := by
  unfold tailWord_857764
  simp only [CollatzResearch.WordTrace]
  refine ⟨15642611632237498636646173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20856815509649998182194897 15642611632237498636646173)
  ·
    refine ⟨5865979362089061988742315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15642611632237498636646173 5865979362089061988742315)
    ·
      refine ⟨8798969043133592983113473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5865979362089061988742315 8798969043133592983113473)
      ·
        refine ⟨6599226782350194737335105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8798969043133592983113473 6599226782350194737335105)
        ·
          refine ⟨4949420086762646053001329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6599226782350194737335105 4949420086762646053001329)
          ·
            refine ⟨3712065065071984539750997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4949420086762646053001329 3712065065071984539750997)
            ·
              refine ⟨43500762481312318825207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3712065065071984539750997 43500762481312318825207)
              ·
                rfl

theorem cell20_857764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 8].length) (baseStart_857764 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_857764 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_857764 prefixEnd_857764 := by exact prefixLift 857764
  have htrace : WordTrace (prefixWord ++ tailWord_857764) baseStart_857764 baseEnd_857764 := by
    simpa [prefixWord, tailWord_857764, baseEnd_857764] using wordTrace_append hprefix tailTrace_857764
  have hstable : (prefixWord ++ tailWord_857764).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_857764).length < 2 ^ (prefixWord ++ tailWord_857764).sum := by decide
  have hdescent : baseEnd_857764 < baseStart_857764 := by decide
  rcases family_descends (prefixWord ++ tailWord_857764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_857825 : List Nat := [1, 2, 3, 1, 6, 1, 2, 2, 2]
def baseStart_857825 : Nat := 118140960795 + 857825 * 2 ^ 59
def prefixEnd_857825 : Nat := 4983230072969 + 3 ^ 40 * 857825 * 2
def baseEnd_857825 : Nat := 391534704393965768393281

theorem tailTrace_857825 : CollatzResearch.WordTrace tailWord_857825 prefixEnd_857825 391534704393965768393281 := by
  unfold tailWord_857825
  simp only [CollatzResearch.WordTrace]
  refine ⟨31287448117254004691262929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20858298744836003127508619 31287448117254004691262929)
  ·
    refine ⟨23465586087940503518447197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31287448117254004691262929 23465586087940503518447197)
    ·
      refine ⟨8799594782977688819417699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23465586087940503518447197 8799594782977688819417699)
      ·
        refine ⟨13199392174466533229126549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8799594782977688819417699 13199392174466533229126549)
        ·
          refine ⟨618721508178118745115307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 13199392174466533229126549 618721508178118745115307)
          ·
            refine ⟨928082262267178117672961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 618721508178118745115307 928082262267178117672961)
            ·
              refine ⟨696061696700383588254721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 928082262267178117672961 696061696700383588254721)
              ·
                refine ⟨522046272525287691191041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 696061696700383588254721 522046272525287691191041)
                ·
                  refine ⟨391534704393965768393281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 522046272525287691191041 391534704393965768393281)
                  ·
                    rfl

theorem cell20_857825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 2, 2, 2].length) (baseStart_857825 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_857825 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_857825 prefixEnd_857825 := by exact prefixLift 857825
  have htrace : WordTrace (prefixWord ++ tailWord_857825) baseStart_857825 baseEnd_857825 := by
    simpa [prefixWord, tailWord_857825, baseEnd_857825] using wordTrace_append hprefix tailTrace_857825
  have hstable : (prefixWord ++ tailWord_857825).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_857825).length < 2 ^ (prefixWord ++ tailWord_857825).sum := by decide
  have hdescent : baseEnd_857825 < baseStart_857825 := by decide
  rcases family_descends (prefixWord ++ tailWord_857825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_857888 : List Nat := [2, 1, 1, 5, 1, 1, 1, 6, 2]
def baseStart_857888 : Nat := 118140960795 + 857888 * 2 ^ 59
def prefixEnd_857888 : Nat := 4983230072969 + 3 ^ 40 * 857888 * 2
def baseEnd_857888 : Nat := 391563459310617549293023

theorem tailTrace_857888 : CollatzResearch.WordTrace tailWord_857888 prefixEnd_857888 391563459310617549293023 := by
  unfold tailWord_857888
  simp only [CollatzResearch.WordTrace]
  refine ⟨15644872958012883225403159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20859830610683844300537545 15644872958012883225403159)
  ·
    refine ⟨23467309437019324838104739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15644872958012883225403159 23467309437019324838104739)
    ·
      refine ⟨35200964155528987257157109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23467309437019324838104739 35200964155528987257157109)
      ·
        refine ⟨3300090389580842555358479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 35200964155528987257157109 3300090389580842555358479)
        ·
          refine ⟨4950135584371263833037719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3300090389580842555358479 4950135584371263833037719)
          ·
            refine ⟨7425203376556895749556579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4950135584371263833037719 7425203376556895749556579)
            ·
              refine ⟨11137805064835343624334869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7425203376556895749556579 11137805064835343624334869)
              ·
                refine ⟨522084612414156732390697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 11137805064835343624334869 522084612414156732390697)
                ·
                  refine ⟨391563459310617549293023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 522084612414156732390697 391563459310617549293023)
                  ·
                    rfl

theorem cell20_857888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 6, 2].length) (baseStart_857888 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_857888 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_857888 prefixEnd_857888 := by exact prefixLift 857888
  have htrace : WordTrace (prefixWord ++ tailWord_857888) baseStart_857888 baseEnd_857888 := by
    simpa [prefixWord, tailWord_857888, baseEnd_857888] using wordTrace_append hprefix tailTrace_857888
  have hstable : (prefixWord ++ tailWord_857888).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_857888).length < 2 ^ (prefixWord ++ tailWord_857888).sum := by decide
  have hdescent : baseEnd_857888 < baseStart_857888 := by decide
  rcases family_descends (prefixWord ++ tailWord_857888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_857923 : List Nat := [1, 1, 1, 3, 1, 5, 1, 2, 5]
def baseStart_857923 : Nat := 118140960795 + 857923 * 2 ^ 59
def prefixEnd_857923 : Nat := 4983230072969 + 3 ^ 40 * 857923 * 2
def baseEnd_857923 : Nat := 391579434264312983126213

theorem tailTrace_857923 : CollatzResearch.WordTrace tailWord_857923 prefixEnd_857923 391579434264312983126213 := by
  unfold tailWord_857923
  simp only [CollatzResearch.WordTrace]
  refine ⟨31291022470898967428330423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20860681647265978285553615 31291022470898967428330423)
  ·
    refine ⟨46936533706348451142495635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31291022470898967428330423 46936533706348451142495635)
    ·
      refine ⟨70404800559522676713743453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46936533706348451142495635 70404800559522676713743453)
      ·
        refine ⟨26401800209821003767653795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70404800559522676713743453 26401800209821003767653795)
        ·
          refine ⟨39602700314731505651480693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26401800209821003767653795 39602700314731505651480693)
          ·
            refine ⟨3712753154506078654826315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 39602700314731505651480693 3712753154506078654826315)
            ·
              refine ⟨5569129731759117982239473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3712753154506078654826315 5569129731759117982239473)
              ·
                refine ⟨4176847298819338486679605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5569129731759117982239473 4176847298819338486679605)
                ·
                  refine ⟨391579434264312983126213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4176847298819338486679605 391579434264312983126213)
                  ·
                    rfl

theorem cell20_857923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 2, 5].length) (baseStart_857923 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_857923 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_857923 prefixEnd_857923 := by exact prefixLift 857923
  have htrace : WordTrace (prefixWord ++ tailWord_857923) baseStart_857923 baseEnd_857923 := by
    simpa [prefixWord, tailWord_857923, baseEnd_857923] using wordTrace_append hprefix tailTrace_857923
  have hstable : (prefixWord ++ tailWord_857923).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_857923).length < 2 ^ (prefixWord ++ tailWord_857923).sum := by decide
  have hdescent : baseEnd_857923 < baseStart_857923 := by decide
  rcases family_descends (prefixWord ++ tailWord_857923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_857933 : List Nat := [1, 6, 1, 2, 1, 1, 8]
def baseStart_857933 : Nat := 118140960795 + 857933 * 2 ^ 59
def prefixEnd_857933 : Nat := 4983230072969 + 3 ^ 40 * 857933 * 2
def baseEnd_857933 : Nat := 43509333170755265865871

theorem tailTrace_857933 : CollatzResearch.WordTrace tailWord_857933 prefixEnd_857933 43509333170755265865871 := by
  unfold tailWord_857933
  simp only [CollatzResearch.WordTrace]
  refine ⟨31291387200862739136194453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20860924800575159424129635 31291387200862739136194453)
  ·
    refine ⟨1466783775040440897009115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 31291387200862739136194453 1466783775040440897009115)
    ·
      refine ⟨2200175662560661345513673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1466783775040440897009115 2200175662560661345513673)
      ·
        refine ⟨1650131746920496009135255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2200175662560661345513673 1650131746920496009135255)
        ·
          refine ⟨2475197620380744013702883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1650131746920496009135255 2475197620380744013702883)
          ·
            refine ⟨3712796430571116020554325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2475197620380744013702883 3712796430571116020554325)
            ·
              refine ⟨43509333170755265865871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3712796430571116020554325 43509333170755265865871)
              ·
                rfl

theorem cell20_857933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 8].length) (baseStart_857933 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_857933 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_857933 prefixEnd_857933 := by exact prefixLift 857933
  have htrace : WordTrace (prefixWord ++ tailWord_857933) baseStart_857933 baseEnd_857933 := by
    simpa [prefixWord, tailWord_857933, baseEnd_857933] using wordTrace_append hprefix tailTrace_857933
  have hstable : (prefixWord ++ tailWord_857933).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_857933).length < 2 ^ (prefixWord ++ tailWord_857933).sum := by decide
  have hdescent : baseEnd_857933 < baseStart_857933 := by decide
  rcases family_descends (prefixWord ++ tailWord_857933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_857940 : List Nat := [2, 4, 1, 1, 3, 1, 2, 1, 5]
def baseStart_857940 : Nat := 118140960795 + 857940 * 2 ^ 59
def prefixEnd_857940 : Nat := 4983230072969 + 3 ^ 40 * 857940 * 2
def baseEnd_857940 : Nat := 391587193527536479559477

theorem tailTrace_857940 : CollatzResearch.WordTrace tailWord_857940 prefixEnd_857940 391587193527536479559477 := by
  unfold tailWord_857940
  simp only [CollatzResearch.WordTrace]
  refine ⟨15645821255918689665849637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20861095007891586221132849 15645821255918689665849637)
  ·
    refine ⟨2933591485484754312346807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15645821255918689665849637 2933591485484754312346807)
    ·
      refine ⟨4400387228227131468520211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2933591485484754312346807 4400387228227131468520211)
      ·
        refine ⟨6600580842340697202780317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4400387228227131468520211 6600580842340697202780317)
        ·
          refine ⟨2475217815877761451042619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6600580842340697202780317 2475217815877761451042619)
          ·
            refine ⟨3712826723816642176563929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2475217815877761451042619 3712826723816642176563929)
            ·
              refine ⟨2784620042862481632422947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3712826723816642176563929 2784620042862481632422947)
              ·
                refine ⟨4176930064293722448634421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2784620042862481632422947 4176930064293722448634421)
                ·
                  refine ⟨391587193527536479559477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4176930064293722448634421 391587193527536479559477)
                  ·
                    rfl

theorem cell20_857940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 2, 1, 5].length) (baseStart_857940 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_857940 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_857940 prefixEnd_857940 := by exact prefixLift 857940
  have htrace : WordTrace (prefixWord ++ tailWord_857940) baseStart_857940 baseEnd_857940 := by
    simpa [prefixWord, tailWord_857940, baseEnd_857940] using wordTrace_append hprefix tailTrace_857940
  have hstable : (prefixWord ++ tailWord_857940).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_857940).length < 2 ^ (prefixWord ++ tailWord_857940).sum := by decide
  have hdescent : baseEnd_857940 < baseStart_857940 := by decide
  rcases family_descends (prefixWord ++ tailWord_857940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_857943 : List Nat := [1, 1, 3, 2, 6, 1, 1, 1, 4]
def baseStart_857943 : Nat := 118140960795 + 857943 * 2 ^ 59
def prefixEnd_857943 : Nat := 4983230072969 + 3 ^ 40 * 857943 * 2
def baseEnd_857943 : Nat := 391588562809281802459465

theorem tailTrace_857943 : CollatzResearch.WordTrace tailWord_857943 prefixEnd_857943 391588562809281802459465 := by
  unfold tailWord_857943
  simp only [CollatzResearch.WordTrace]
  refine ⟨31291751930826510844058483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20861167953884340562705655 31291751930826510844058483)
  ·
    refine ⟨46937627896239766266087725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31291751930826510844058483 46937627896239766266087725)
    ·
      refine ⟨17601610461089912349782897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46937627896239766266087725 17601610461089912349782897)
      ·
        refine ⟨13201207845817434262337173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17601610461089912349782897 13201207845817434262337173)
        ·
          refine ⟨618806617772692231047055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 13201207845817434262337173 618806617772692231047055)
          ·
            refine ⟨928209926659038346570583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 618806617772692231047055 928209926659038346570583)
            ·
              refine ⟨1392314889988557519855875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 928209926659038346570583 1392314889988557519855875)
              ·
                refine ⟨2088472334982836279783813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1392314889988557519855875 2088472334982836279783813)
                ·
                  refine ⟨391588562809281802459465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2088472334982836279783813 391588562809281802459465)
                  ·
                    rfl

theorem cell20_857943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 1, 1, 4].length) (baseStart_857943 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_857943 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_857943 prefixEnd_857943 := by exact prefixLift 857943
  have htrace : WordTrace (prefixWord ++ tailWord_857943) baseStart_857943 baseEnd_857943 := by
    simpa [prefixWord, tailWord_857943, baseEnd_857943] using wordTrace_append hprefix tailTrace_857943
  have hstable : (prefixWord ++ tailWord_857943).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_857943).length < 2 ^ (prefixWord ++ tailWord_857943).sum := by decide
  have hdescent : baseEnd_857943 < baseStart_857943 := by decide
  rcases family_descends (prefixWord ++ tailWord_857943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_857968 : List Nat := [2, 1, 1, 1, 4, 1, 1, 3, 6]
def baseStart_857968 : Nat := 118140960795 + 857968 * 2 ^ 59
def prefixEnd_857968 : Nat := 4983230072969 + 3 ^ 40 * 857968 * 2
def baseEnd_857968 : Nat := 391599973490492826626029

theorem tailTrace_857968 : CollatzResearch.WordTrace tailWord_857968 prefixEnd_857968 391599973490492826626029 := by
  unfold tailWord_857968
  simp only [CollatzResearch.WordTrace]
  refine ⟨15646331877867970056859279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20861775837157293409145705 15646331877867970056859279)
  ·
    refine ⟨23469497816801955085288919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15646331877867970056859279 23469497816801955085288919)
    ·
      refine ⟨35204246725202932627933379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23469497816801955085288919 35204246725202932627933379)
      ·
        refine ⟨52806370087804398941900069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35204246725202932627933379 52806370087804398941900069)
        ·
          refine ⟨9901194391463324801606263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52806370087804398941900069 9901194391463324801606263)
          ·
            refine ⟨14851791587194987202409395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9901194391463324801606263 14851791587194987202409395)
            ·
              refine ⟨22277687380792480803614093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14851791587194987202409395 22277687380792480803614093)
              ·
                refine ⟨8354132767797180301355285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22277687380792480803614093 8354132767797180301355285)
                ·
                  refine ⟨391599973490492826626029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8354132767797180301355285 391599973490492826626029)
                  ·
                    rfl

theorem cell20_857968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 3, 6].length) (baseStart_857968 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_857968 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_857968 prefixEnd_857968 := by exact prefixLift 857968
  have htrace : WordTrace (prefixWord ++ tailWord_857968) baseStart_857968 baseEnd_857968 := by
    simpa [prefixWord, tailWord_857968, baseEnd_857968] using wordTrace_append hprefix tailTrace_857968
  have hstable : (prefixWord ++ tailWord_857968).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_857968).length < 2 ^ (prefixWord ++ tailWord_857968).sum := by decide
  have hdescent : baseEnd_857968 < baseStart_857968 := by decide
  rcases family_descends (prefixWord ++ tailWord_857968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_857992 : List Nat := [2, 1, 3, 3, 3, 8]
def baseStart_857992 : Nat := 118140960795 + 857992 * 2 ^ 59
def prefixEnd_857992 : Nat := 4983230072969 + 3 ^ 40 * 857992 * 2
def baseEnd_857992 : Nat := 14504108434979829993553

theorem tailTrace_857992 : CollatzResearch.WordTrace tailWord_857992 prefixEnd_857992 14504108434979829993553 := by
  unfold tailWord_857992
  simp only [CollatzResearch.WordTrace]
  refine ⟨15646769553824496106296115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20862359405099328141728153 15646769553824496106296115)
  ·
    refine ⟨23470154330736744159444173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15646769553824496106296115 23470154330736744159444173)
    ·
      refine ⟨8801307874026279059791565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23470154330736744159444173 8801307874026279059791565)
      ·
        refine ⟨3300490452759854647421837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8801307874026279059791565 3300490452759854647421837)
        ·
          refine ⟨1237683919784945492783189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3300490452759854647421837 1237683919784945492783189)
          ·
            refine ⟨14504108434979829993553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1237683919784945492783189 14504108434979829993553)
            ·
              rfl

theorem cell20_857992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 8].length) (baseStart_857992 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_857992 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_857992 prefixEnd_857992 := by exact prefixLift 857992
  have htrace : WordTrace (prefixWord ++ tailWord_857992) baseStart_857992 baseEnd_857992 := by
    simpa [prefixWord, tailWord_857992, baseEnd_857992] using wordTrace_append hprefix tailTrace_857992
  have hstable : (prefixWord ++ tailWord_857992).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_857992).length < 2 ^ (prefixWord ++ tailWord_857992).sum := by decide
  have hdescent : baseEnd_857992 < baseStart_857992 := by decide
  rcases family_descends (prefixWord ++ tailWord_857992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_857998 : List Nat := [4, 1, 1, 5, 1, 1, 1, 4, 2]
def baseStart_857998 : Nat := 118140960795 + 857998 * 2 ^ 59
def prefixEnd_857998 : Nat := 4983230072969 + 3 ^ 40 * 857998 * 2
def baseEnd_857998 : Nat := 391613666307946055625907

theorem tailTrace_857998 : CollatzResearch.WordTrace tailWord_857998 prefixEnd_857998 391613666307946055625907 := by
  unfold tailWord_857998
  simp only [CollatzResearch.WordTrace]
  refine ⟨3911719743203406904663831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20862505297084836824873765 3911719743203406904663831)
  ·
    refine ⟨5867579614805110356995747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3911719743203406904663831 5867579614805110356995747)
    ·
      refine ⟨8801369422207665535493621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5867579614805110356995747 8801369422207665535493621)
      ·
        refine ⟨825128383331968643952527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8801369422207665535493621 825128383331968643952527)
        ·
          refine ⟨1237692574997952965928791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 825128383331968643952527 1237692574997952965928791)
          ·
            refine ⟨1856538862496929448893187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1237692574997952965928791 1856538862496929448893187)
            ·
              refine ⟨2784808293745394173339781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1856538862496929448893187 2784808293745394173339781)
              ·
                refine ⟨522151555077261407501209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2784808293745394173339781 522151555077261407501209)
                ·
                  refine ⟨391613666307946055625907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 522151555077261407501209 391613666307946055625907)
                  ·
                    rfl

theorem cell20_857998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 1, 4, 2].length) (baseStart_857998 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_857998 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_857998 prefixEnd_857998 := by exact prefixLift 857998
  have htrace : WordTrace (prefixWord ++ tailWord_857998) baseStart_857998 baseEnd_857998 := by
    simpa [prefixWord, tailWord_857998, baseEnd_857998] using wordTrace_append hprefix tailTrace_857998
  have hstable : (prefixWord ++ tailWord_857998).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_857998).length < 2 ^ (prefixWord ++ tailWord_857998).sum := by decide
  have hdescent : baseEnd_857998 < baseStart_857998 := by decide
  rcases family_descends (prefixWord ++ tailWord_857998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_858023 : List Nat := [1, 1, 6, 1, 2, 1, 1, 1, 6]
def baseStart_858023 : Nat := 118140960795 + 858023 * 2 ^ 59
def prefixEnd_858023 : Nat := 4983230072969 + 3 ^ 40 * 858023 * 2
def baseEnd_858023 : Nat := 391625076989157079792471

theorem tailTrace_858023 : CollatzResearch.WordTrace tailWord_858023 prefixEnd_858023 391625076989157079792471 := by
  unfold tailWord_858023
  simp only [CollatzResearch.WordTrace]
  refine ⟨31294669770536684506970723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20863113180357789671313815 31294669770536684506970723)
  ·
    refine ⟨46942004655805026760456085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31294669770536684506970723 46942004655805026760456085)
    ·
      refine ⟨2200406468240860629396379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 46942004655805026760456085 2200406468240860629396379)
      ·
        refine ⟨3300609702361290944094569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2200406468240860629396379 3300609702361290944094569)
        ·
          refine ⟨2475457276770968208070927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3300609702361290944094569 2475457276770968208070927)
          ·
            refine ⟨3713185915156452312106391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2475457276770968208070927 3713185915156452312106391)
            ·
              refine ⟨5569778872734678468159587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3713185915156452312106391 5569778872734678468159587)
              ·
                refine ⟨8354668309102017702239381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5569778872734678468159587 8354668309102017702239381)
                ·
                  refine ⟨391625076989157079792471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8354668309102017702239381 391625076989157079792471)
                  ·
                    rfl

theorem cell20_858023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 1, 6].length) (baseStart_858023 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_858023 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_858023 prefixEnd_858023 := by exact prefixLift 858023
  have htrace : WordTrace (prefixWord ++ tailWord_858023) baseStart_858023 baseEnd_858023 := by
    simpa [prefixWord, tailWord_858023, baseEnd_858023] using wordTrace_append hprefix tailTrace_858023
  have hstable : (prefixWord ++ tailWord_858023).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_858023).length < 2 ^ (prefixWord ++ tailWord_858023).sum := by decide
  have hdescent : baseEnd_858023 < baseStart_858023 := by decide
  rcases family_descends (prefixWord ++ tailWord_858023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_858040 : List Nat := [2, 1, 2, 1, 2, 3, 4, 3, 2]
def baseStart_858040 : Nat := 118140960795 + 858040 * 2 ^ 59
def prefixEnd_858040 : Nat := 4983230072969 + 3 ^ 40 * 858040 * 2
def baseEnd_858040 : Nat := 391632836252380576225735

theorem tailTrace_858040 : CollatzResearch.WordTrace tailWord_858040 prefixEnd_858040 391632836252380576225735 := by
  unfold tailWord_858040
  simp only [CollatzResearch.WordTrace]
  refine ⟨15647644905737548205169787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20863526540983397606893049 15647644905737548205169787)
  ·
    refine ⟨23471467358606322307754681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15647644905737548205169787 23471467358606322307754681)
    ·
      refine ⟨17603600518954741730816011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23471467358606322307754681 17603600518954741730816011)
      ·
        refine ⟨26405400778432112596224017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17603600518954741730816011 26405400778432112596224017)
        ·
          refine ⟨19804050583824084447168013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26405400778432112596224017 19804050583824084447168013)
          ·
            refine ⟨7426518968934031667688005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19804050583824084447168013 7426518968934031667688005)
            ·
              refine ⟨1392472306675130937691501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7426518968934031667688005 1392472306675130937691501)
              ·
                refine ⟨522177115003174101634313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1392472306675130937691501 522177115003174101634313)
                ·
                  refine ⟨391632836252380576225735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 522177115003174101634313 391632836252380576225735)
                  ·
                    rfl

theorem cell20_858040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 4, 3, 2].length) (baseStart_858040 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_858040 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_858040 prefixEnd_858040 := by exact prefixLift 858040
  have htrace : WordTrace (prefixWord ++ tailWord_858040) baseStart_858040 baseEnd_858040 := by
    simpa [prefixWord, tailWord_858040, baseEnd_858040] using wordTrace_append hprefix tailTrace_858040
  have hstable : (prefixWord ++ tailWord_858040).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_858040).length < 2 ^ (prefixWord ++ tailWord_858040).sum := by decide
  have hdescent : baseEnd_858040 < baseStart_858040 := by decide
  rcases family_descends (prefixWord ++ tailWord_858040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_858068 : List Nat := [2, 4, 1, 2, 1, 1, 2, 7]
def baseStart_858068 : Nat := 118140960795 + 858068 * 2 ^ 59
def prefixEnd_858068 : Nat := 4983230072969 + 3 ^ 40 * 858068 * 2
def baseEnd_858068 : Nat := 130548538738445641097429

theorem tailTrace_858068 : CollatzResearch.WordTrace tailWord_858068 prefixEnd_858068 130548538738445641097429 := by
  unfold tailWord_858068
  simp only [CollatzResearch.WordTrace]
  refine ⟨15648155527686828596179429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20864207370249104794905905 15648155527686828596179429)
  ·
    refine ⟨2934029161441280361783643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15648155527686828596179429 2934029161441280361783643)
    ·
      refine ⟨4401043742161920542675465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2934029161441280361783643 4401043742161920542675465)
      ·
        refine ⟨3300782806621440407006599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4401043742161920542675465 3300782806621440407006599)
        ·
          refine ⟨4951174209932160610509899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3300782806621440407006599 4951174209932160610509899)
          ·
            refine ⟨7426761314898240915764849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4951174209932160610509899 7426761314898240915764849)
            ·
              refine ⟨5570070986173680686823637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7426761314898240915764849 5570070986173680686823637)
              ·
                refine ⟨130548538738445641097429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5570070986173680686823637 130548538738445641097429)
                ·
                  rfl

theorem cell20_858068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 7].length) (baseStart_858068 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_858068 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_858068 prefixEnd_858068 := by exact prefixLift 858068
  have htrace : WordTrace (prefixWord ++ tailWord_858068) baseStart_858068 baseEnd_858068 := by
    simpa [prefixWord, tailWord_858068, baseEnd_858068] using wordTrace_append hprefix tailTrace_858068
  have hstable : (prefixWord ++ tailWord_858068).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_858068).length < 2 ^ (prefixWord ++ tailWord_858068).sum := by decide
  have hdescent : baseEnd_858068 < baseStart_858068 := by decide
  rcases family_descends (prefixWord ++ tailWord_858068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_858102 : List Nat := [5, 1, 1, 1, 5, 1, 6]
def baseStart_858102 : Nat := 118140960795 + 858102 * 2 ^ 59
def prefixEnd_858102 : Nat := 4983230072969 + 3 ^ 40 * 858102 * 2
def baseEnd_858102 : Nat := 43517903860198212906535

theorem tailTrace_858102 : CollatzResearch.WordTrace tailWord_858102 prefixEnd_858102 43517903860198212906535 := by
  unfold tailWord_858102
  simp only [CollatzResearch.WordTrace]
  refine ⟨1956096946078155062443535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20865034091500320666064373 1956096946078155062443535)
  ·
    refine ⟨2934145419117232593665303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1956096946078155062443535 2934145419117232593665303)
    ·
      refine ⟨4401218128675848890497955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2934145419117232593665303 4401218128675848890497955)
      ·
        refine ⟨6601827193013773335746933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4401218128675848890497955 6601827193013773335746933)
        ·
          refine ⟨618921299345041250226275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6601827193013773335746933 618921299345041250226275)
          ·
            refine ⟨928381949017561875339413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 618921299345041250226275 928381949017561875339413)
            ·
              refine ⟨43517903860198212906535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 928381949017561875339413 43517903860198212906535)
              ·
                rfl

theorem cell20_858102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 6].length) (baseStart_858102 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_858102 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_858102 prefixEnd_858102 := by exact prefixLift 858102
  have htrace : WordTrace (prefixWord ++ tailWord_858102) baseStart_858102 baseEnd_858102 := by
    simpa [prefixWord, tailWord_858102, baseEnd_858102] using wordTrace_append hprefix tailTrace_858102
  have hstable : (prefixWord ++ tailWord_858102).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_858102).length < 2 ^ (prefixWord ++ tailWord_858102).sum := by decide
  have hdescent : baseEnd_858102 < baseStart_858102 := by decide
  rcases family_descends (prefixWord ++ tailWord_858102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_858113 : List Nat := [1, 2, 4, 1, 2, 1, 1, 3, 5]
def baseStart_858113 : Nat := 118140960795 + 858113 * 2 ^ 59
def prefixEnd_858113 : Nat := 4983230072969 + 3 ^ 40 * 858113 * 2
def baseEnd_858113 : Nat := 391666155441516766792103

theorem tailTrace_858113 : CollatzResearch.WordTrace tailWord_858113 prefixEnd_858113 391666155441516766792103 := by
  unfold tailWord_858113
  simp only [CollatzResearch.WordTrace]
  refine ⟨31297952340210629877746993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20865301560140419918497995 31297952340210629877746993)
  ·
    refine ⟨23473464255157972408310245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31297952340210629877746993 23473464255157972408310245)
    ·
      refine ⟨4401274547842119826558171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23473464255157972408310245 4401274547842119826558171)
      ·
        refine ⟨6601911821763179739837257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4401274547842119826558171 6601911821763179739837257)
        ·
          refine ⟨4951433866322384804877943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6601911821763179739837257 4951433866322384804877943)
          ·
            refine ⟨7427150799483577207316915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4951433866322384804877943 7427150799483577207316915)
            ·
              refine ⟨11140726199225365810975373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7427150799483577207316915 11140726199225365810975373)
              ·
                refine ⟨4177772324709512179115765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11140726199225365810975373 4177772324709512179115765)
                ·
                  refine ⟨391666155441516766792103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4177772324709512179115765 391666155441516766792103)
                  ·
                    rfl

theorem cell20_858113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 3, 5].length) (baseStart_858113 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_858113 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_858113 prefixEnd_858113 := by exact prefixLift 858113
  have htrace : WordTrace (prefixWord ++ tailWord_858113) baseStart_858113 baseEnd_858113 := by
    simpa [prefixWord, tailWord_858113, baseEnd_858113] using wordTrace_append hprefix tailTrace_858113
  have hstable : (prefixWord ++ tailWord_858113).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_858113).length < 2 ^ (prefixWord ++ tailWord_858113).sum := by decide
  have hdescent : baseEnd_858113 < baseStart_858113 := by decide
  rcases family_descends (prefixWord ++ tailWord_858113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_858118 : List Nat := [6, 2, 1, 2, 2, 1, 2, 1, 3]
def baseStart_858118 : Nat := 118140960795 + 858118 * 2 ^ 59
def prefixEnd_858118 : Nat := 4983230072969 + 3 ^ 40 * 858118 * 2
def baseEnd_858118 : Nat := 391668437577758971625417

theorem tailTrace_858118 : CollatzResearch.WordTrace tailWord_858118 prefixEnd_858118 391668437577758971625417 := by
  unfold tailWord_858118
  simp only [CollatzResearch.WordTrace]
  refine ⟨978066709537266116614969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 20865423136795010487786005 978066709537266116614969)
  ·
    refine ⟨733550032152949587461227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 978066709537266116614969 733550032152949587461227)
    ·
      refine ⟨1100325048229424381191841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 733550032152949587461227 1100325048229424381191841)
      ·
        refine ⟨825243786172068285893881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1100325048229424381191841 825243786172068285893881)
        ·
          refine ⟨618932839629051214420411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 825243786172068285893881 618932839629051214420411)
          ·
            refine ⟨928399259443576821630617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 618932839629051214420411 928399259443576821630617)
            ·
              refine ⟨696299444582682616222963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 928399259443576821630617 696299444582682616222963)
              ·
                refine ⟨1044449166874023924334445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 696299444582682616222963 1044449166874023924334445)
                ·
                  refine ⟨391668437577758971625417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1044449166874023924334445 391668437577758971625417)
                  ·
                    rfl

theorem cell20_858118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 2, 1, 3].length) (baseStart_858118 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_858118 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_858118 prefixEnd_858118 := by exact prefixLift 858118
  have htrace : WordTrace (prefixWord ++ tailWord_858118) baseStart_858118 baseEnd_858118 := by
    simpa [prefixWord, tailWord_858118, baseEnd_858118] using wordTrace_append hprefix tailTrace_858118
  have hstable : (prefixWord ++ tailWord_858118).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_858118).length < 2 ^ (prefixWord ++ tailWord_858118).sum := by decide
  have hdescent : baseEnd_858118 < baseStart_858118 := by decide
  rcases family_descends (prefixWord ++ tailWord_858118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_858164 : List Nat := [2, 5, 1, 2, 2, 1, 2, 2, 3]
def baseStart_858164 : Nat := 118140960795 + 858164 * 2 ^ 59
def prefixEnd_858164 : Nat := 4983230072969 + 3 ^ 40 * 858164 * 2
def baseEnd_858164 : Nat := 391689433231187256091895

theorem tailTrace_858164 : CollatzResearch.WordTrace tailWord_858164 prefixEnd_858164 391689433231187256091895 := by
  unfold tailWord_858164
  simp only [CollatzResearch.WordTrace]
  refine ⟨15649906231512932793926773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20866541642017243725235697 15649906231512932793926773)
  ·
    refine ⟨1467178709204337449430635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15649906231512932793926773 1467178709204337449430635)
    ·
      refine ⟨2200768063806506174145953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1467178709204337449430635 2200768063806506174145953)
      ·
        refine ⟨1650576047854879630609465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2200768063806506174145953 1650576047854879630609465)
        ·
          refine ⟨1237932035891159722957099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1650576047854879630609465 1237932035891159722957099)
          ·
            refine ⟨1856898053836739584435649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1237932035891159722957099 1856898053836739584435649)
            ·
              refine ⟨1392673540377554688326737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1856898053836739584435649 1392673540377554688326737)
              ·
                refine ⟨1044505155283166016245053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1392673540377554688326737 1044505155283166016245053)
                ·
                  refine ⟨391689433231187256091895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1044505155283166016245053 391689433231187256091895)
                  ·
                    rfl

theorem cell20_858164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 2, 2, 3].length) (baseStart_858164 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_858164 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_858164 prefixEnd_858164 := by exact prefixLift 858164
  have htrace : WordTrace (prefixWord ++ tailWord_858164) baseStart_858164 baseEnd_858164 := by
    simpa [prefixWord, tailWord_858164, baseEnd_858164] using wordTrace_append hprefix tailTrace_858164
  have hstable : (prefixWord ++ tailWord_858164).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_858164).length < 2 ^ (prefixWord ++ tailWord_858164).sum := by decide
  have hdescent : baseEnd_858164 < baseStart_858164 := by decide
  rcases family_descends (prefixWord ++ tailWord_858164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_858230 : List Nat := [5, 1, 1, 2, 1, 3, 2, 1, 4]
def baseStart_858230 : Nat := 118140960795 + 858230 * 2 ^ 59
def prefixEnd_858230 : Nat := 4983230072969 + 3 ^ 40 * 858230 * 2
def baseEnd_858230 : Nat := 391719557429584359891625

theorem tailTrace_858230 : CollatzResearch.WordTrace tailWord_858230 prefixEnd_858230 391719557429584359891625 := by
  unfold tailWord_858230
  simp only [CollatzResearch.WordTrace]
  refine ⟨1956388730049172428734759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20868146453857839239837429 1956388730049172428734759)
  ·
    refine ⟨2934583095073758643102139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1956388730049172428734759 2934583095073758643102139)
    ·
      refine ⟨4401874642610637964653209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2934583095073758643102139 4401874642610637964653209)
      ·
        refine ⟨3301405981957978473489907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4401874642610637964653209 3301405981957978473489907)
        ·
          refine ⟨4952108972936967710234861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3301405981957978473489907 4952108972936967710234861)
          ·
            refine ⟨1857040864851362891338073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4952108972936967710234861 1857040864851362891338073)
            ·
              refine ⟨1392780648638522168503555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1857040864851362891338073 1392780648638522168503555)
              ·
                refine ⟨2089170972957783252755333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1392780648638522168503555 2089170972957783252755333)
                ·
                  refine ⟨391719557429584359891625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2089170972957783252755333 391719557429584359891625)
                  ·
                    rfl

theorem cell20_858230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 2, 1, 4].length) (baseStart_858230 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_858230 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_858230 prefixEnd_858230 := by exact prefixLift 858230
  have htrace : WordTrace (prefixWord ++ tailWord_858230) baseStart_858230 baseEnd_858230 := by
    simpa [prefixWord, tailWord_858230, baseEnd_858230] using wordTrace_append hprefix tailTrace_858230
  have hstable : (prefixWord ++ tailWord_858230).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_858230).length < 2 ^ (prefixWord ++ tailWord_858230).sum := by decide
  have hdescent : baseEnd_858230 < baseStart_858230 := by decide
  rcases family_descends (prefixWord ++ tailWord_858230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_858254 : List Nat := [4, 1, 1, 3, 3, 2, 2, 4]
def baseStart_858254 : Nat := 118140960795 + 858254 * 2 ^ 59
def prefixEnd_858254 : Nat := 4983230072969 + 3 ^ 40 * 858254 * 2
def baseEnd_858254 : Nat := 130576837227848981030509

theorem tailTrace_858254 : CollatzResearch.WordTrace tailWord_858254 prefixEnd_858254 130576837227848981030509 := by
  unfold tailWord_858254
  simp only [CollatzResearch.WordTrace]
  refine ⟨3912886879087476369828727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20868730021799873972419877 3912886879087476369828727)
  ·
    refine ⟨5869330318631214554743091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3912886879087476369828727 5869330318631214554743091)
    ·
      refine ⟨8803995477946821832114637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5869330318631214554743091 8803995477946821832114637)
      ·
        refine ⟨3301498304230058187042989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8803995477946821832114637 3301498304230058187042989)
        ·
          refine ⟨1238061864086271820141121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3301498304230058187042989 1238061864086271820141121)
          ·
            refine ⟨928546398064703865105841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1238061864086271820141121 928546398064703865105841)
            ·
              refine ⟨696409798548527898829381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 928546398064703865105841 696409798548527898829381)
              ·
                refine ⟨130576837227848981030509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 696409798548527898829381 130576837227848981030509)
                ·
                  rfl

theorem cell20_858254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 2, 4].length) (baseStart_858254 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_858254 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_858254 prefixEnd_858254 := by exact prefixLift 858254
  have htrace : WordTrace (prefixWord ++ tailWord_858254) baseStart_858254 baseEnd_858254 := by
    simpa [prefixWord, tailWord_858254, baseEnd_858254] using wordTrace_append hprefix tailTrace_858254
  have hstable : (prefixWord ++ tailWord_858254).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_858254).length < 2 ^ (prefixWord ++ tailWord_858254).sum := by decide
  have hdescent : baseEnd_858254 < baseStart_858254 := by decide
  rcases family_descends (prefixWord ++ tailWord_858254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_858258 : List Nat := [3, 2, 3, 1, 1, 1, 3, 6]
def baseStart_858258 : Nat := 118140960795 + 858258 * 2 ^ 59
def prefixEnd_858258 : Nat := 4983230072969 + 3 ^ 40 * 858258 * 2
def baseEnd_858258 : Nat := 130577445797513568986059

theorem tailTrace_858258 : CollatzResearch.WordTrace tailWord_858258 prefixEnd_858258 130577445797513568986059 := by
  unfold tailWord_858258
  simp only [CollatzResearch.WordTrace]
  refine ⟨7825810231171329910443857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20868827283123546427850285 7825810231171329910443857)
  ·
    refine ⟨5869357673378497432832893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7825810231171329910443857 5869357673378497432832893)
    ·
      refine ⟨2201009127516936537312335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5869357673378497432832893 2201009127516936537312335)
      ·
        refine ⟨3301513691275404805968503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2201009127516936537312335 3301513691275404805968503)
        ·
          refine ⟨4952270536913107208952755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3301513691275404805968503 4952270536913107208952755)
          ·
            refine ⟨7428405805369660813429133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4952270536913107208952755 7428405805369660813429133)
            ·
              refine ⟨2785652177013622805035925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7428405805369660813429133 2785652177013622805035925)
              ·
                refine ⟨130577445797513568986059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2785652177013622805035925 130577445797513568986059)
                ·
                  rfl

theorem cell20_858258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 3, 6].length) (baseStart_858258 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_858258 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_858258 prefixEnd_858258 := by exact prefixLift 858258
  have htrace : WordTrace (prefixWord ++ tailWord_858258) baseStart_858258 baseEnd_858258 := by
    simpa [prefixWord, tailWord_858258, baseEnd_858258] using wordTrace_append hprefix tailTrace_858258
  have hstable : (prefixWord ++ tailWord_858258).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_858258).length < 2 ^ (prefixWord ++ tailWord_858258).sum := by decide
  have hdescent : baseEnd_858258 < baseStart_858258 := by decide
  rcases family_descends (prefixWord ++ tailWord_858258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_858264 : List Nat := [2, 1, 2, 4, 4, 1, 1, 3, 2]
def baseStart_858264 : Nat := 118140960795 + 858264 * 2 ^ 59
def prefixEnd_858264 : Nat := 4983230072969 + 3 ^ 40 * 858264 * 2
def baseEnd_858264 : Nat := 391735075956031352758153

theorem tailTrace_858264 : CollatzResearch.WordTrace tailWord_858264 prefixEnd_858264 391735075956031352758153 := by
  unfold tailWord_858264
  simp only [CollatzResearch.WordTrace]
  refine ⟨15651729881331791333246923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20868973175109055110995897 15651729881331791333246923)
  ·
    refine ⟨23477594821997686999870385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15651729881331791333246923 23477594821997686999870385)
    ·
      refine ⟨17608196116498265249902789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23477594821997686999870385 17608196116498265249902789)
      ·
        refine ⟨3301536771843424734356773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17608196116498265249902789 3301536771843424734356773)
        ·
          refine ⟨619038144720642137691895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3301536771843424734356773 619038144720642137691895)
          ·
            refine ⟨928557217080963206537843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 619038144720642137691895 928557217080963206537843)
            ·
              refine ⟨1392835825621444809806765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 928557217080963206537843 1392835825621444809806765)
              ·
                refine ⟨522313434608041803677537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1392835825621444809806765 522313434608041803677537)
                ·
                  refine ⟨391735075956031352758153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 522313434608041803677537 391735075956031352758153)
                  ·
                    rfl

theorem cell20_858264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 1, 3, 2].length) (baseStart_858264 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_858264 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_858264 prefixEnd_858264 := by exact prefixLift 858264
  have htrace : WordTrace (prefixWord ++ tailWord_858264) baseStart_858264 baseEnd_858264 := by
    simpa [prefixWord, tailWord_858264, baseEnd_858264] using wordTrace_append hprefix tailTrace_858264
  have hstable : (prefixWord ++ tailWord_858264).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_858264).length < 2 ^ (prefixWord ++ tailWord_858264).sum := by decide
  have hdescent : baseEnd_858264 < baseStart_858264 := by decide
  rcases family_descends (prefixWord ++ tailWord_858264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_858327 : List Nat := [1, 1, 3, 2, 1, 2, 1, 7, 2]
def baseStart_858327 : Nat := 118140960795 + 858327 * 2 ^ 59
def prefixEnd_858327 : Nat := 4983230072969 + 3 ^ 40 * 858327 * 2
def baseEnd_858327 : Nat := 391763830872683133657895

theorem tailTrace_858327 : CollatzResearch.WordTrace tailWord_858327 prefixEnd_858327 391763830872683133657895 := by
  unfold tailWord_858327
  simp only [CollatzResearch.WordTrace]
  refine ⟨31305757561435344426037235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20870505040956896284024823 31305757561435344426037235)
  ·
    refine ⟨46958636342153016639055853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31305757561435344426037235 46958636342153016639055853)
    ·
      refine ⟨17609488628307381239645945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46958636342153016639055853 17609488628307381239645945)
      ·
        refine ⟨13207116471230535929734459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17609488628307381239645945 13207116471230535929734459)
        ·
          refine ⟨19810674706845803894601689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13207116471230535929734459 19810674706845803894601689)
          ·
            refine ⟨14858006030134352920951267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19810674706845803894601689 14858006030134352920951267)
            ·
              refine ⟨22287009045201529381426901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14858006030134352920951267 22287009045201529381426901)
              ·
                refine ⟨522351774496910844877193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 22287009045201529381426901 522351774496910844877193)
                ·
                  refine ⟨391763830872683133657895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 522351774496910844877193 391763830872683133657895)
                  ·
                    rfl

theorem cell20_858327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 7, 2].length) (baseStart_858327 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_858327 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_858327 prefixEnd_858327 := by exact prefixLift 858327
  have htrace : WordTrace (prefixWord ++ tailWord_858327) baseStart_858327 baseEnd_858327 := by
    simpa [prefixWord, tailWord_858327, baseEnd_858327] using wordTrace_append hprefix tailTrace_858327
  have hstable : (prefixWord ++ tailWord_858327).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_858327).length < 2 ^ (prefixWord ++ tailWord_858327).sum := by decide
  have hdescent : baseEnd_858327 < baseStart_858327 := by decide
  rcases family_descends (prefixWord ++ tailWord_858327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_858344 : List Nat := [2, 1, 4, 1, 2, 3, 1, 4, 2]
def baseStart_858344 : Nat := 118140960795 + 858344 * 2 ^ 59
def prefixEnd_858344 : Nat := 4983230072969 + 3 ^ 40 * 858344 * 2
def baseEnd_858344 : Nat := 391771590135906630091159

theorem tailTrace_858344 : CollatzResearch.WordTrace tailWord_858344 prefixEnd_858344 391771590135906630091159 := by
  unfold tailWord_858344
  simp only [CollatzResearch.WordTrace]
  refine ⟨15653188801186878164703043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20870918401582504219604057 15653188801186878164703043)
  ·
    refine ⟨23479783201780317247054565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15653188801186878164703043 23479783201780317247054565)
    ·
      refine ⟨4402459350333809483822731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23479783201780317247054565 4402459350333809483822731)
      ·
        refine ⟨6603689025500714225734097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4402459350333809483822731 6603689025500714225734097)
        ·
          refine ⟨4952766769125535669300573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6603689025500714225734097 4952766769125535669300573)
          ·
            refine ⟨1857287538422075875987715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4952766769125535669300573 1857287538422075875987715)
            ·
              refine ⟨2785931307633113813981573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1857287538422075875987715 2785931307633113813981573)
              ·
                refine ⟨522362120181208840121545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2785931307633113813981573 522362120181208840121545)
                ·
                  refine ⟨391771590135906630091159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 522362120181208840121545 391771590135906630091159)
                  ·
                    rfl

theorem cell20_858344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 1, 4, 2].length) (baseStart_858344 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_858344 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_858344 prefixEnd_858344 := by exact prefixLift 858344
  have htrace : WordTrace (prefixWord ++ tailWord_858344) baseStart_858344 baseEnd_858344 := by
    simpa [prefixWord, tailWord_858344, baseEnd_858344] using wordTrace_append hprefix tailTrace_858344
  have hstable : (prefixWord ++ tailWord_858344).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_858344).length < 2 ^ (prefixWord ++ tailWord_858344).sum := by decide
  have hdescent : baseEnd_858344 < baseStart_858344 := by decide
  rcases family_descends (prefixWord ++ tailWord_858344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_858348 : List Nat := [2, 2, 1, 1, 2, 3, 2, 3, 4]
def baseStart_858348 : Nat := 118140960795 + 858348 * 2 ^ 59
def prefixEnd_858348 : Nat := 4983230072969 + 3 ^ 40 * 858348 * 2
def baseEnd_858348 : Nat := 391773415844900393957809

theorem tailTrace_858348 : CollatzResearch.WordTrace tailWord_858348 prefixEnd_858348 391773415844900393957809 := by
  unfold tailWord_858348
  simp only [CollatzResearch.WordTrace]
  refine ⟨15653261747179632506275849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20871015662906176675034465 15653261747179632506275849)
  ·
    refine ⟨11739946310384724379706887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15653261747179632506275849 11739946310384724379706887)
    ·
      refine ⟨17609919465577086569560331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11739946310384724379706887 17609919465577086569560331)
      ·
        refine ⟨26414879198365629854340497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17609919465577086569560331 26414879198365629854340497)
        ·
          refine ⟨19811159398774222390755373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26414879198365629854340497 19811159398774222390755373)
          ·
            refine ⟨7429184774540333396533265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19811159398774222390755373 7429184774540333396533265)
            ·
              refine ⟨5571888580905250047399949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7429184774540333396533265 5571888580905250047399949)
              ·
                refine ⟨2089458217839468767774981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5571888580905250047399949 2089458217839468767774981)
                ·
                  refine ⟨391773415844900393957809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2089458217839468767774981 391773415844900393957809)
                  ·
                    rfl

theorem cell20_858348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 4].length) (baseStart_858348 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_858348 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_858348 prefixEnd_858348 := by exact prefixLift 858348
  have htrace : WordTrace (prefixWord ++ tailWord_858348) baseStart_858348 baseEnd_858348 := by
    simpa [prefixWord, tailWord_858348, baseEnd_858348] using wordTrace_append hprefix tailTrace_858348
  have hstable : (prefixWord ++ tailWord_858348).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_858348).length < 2 ^ (prefixWord ++ tailWord_858348).sum := by decide
  have hdescent : baseEnd_858348 < baseStart_858348 := by decide
  rcases family_descends (prefixWord ++ tailWord_858348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_858358 : List Nat := [5, 1, 1, 1, 1, 1, 4, 3, 3]
def baseStart_858358 : Nat := 118140960795 + 858358 * 2 ^ 59
def prefixEnd_858358 : Nat := 4983230072969 + 3 ^ 40 * 858358 * 2
def baseEnd_858358 : Nat := 391777980117384803624435

theorem tailTrace_858358 : CollatzResearch.WordTrace tailWord_858358 prefixEnd_858358 391777980117384803624435 := by
  unfold tailWord_858358
  simp only [CollatzResearch.WordTrace]
  refine ⟨1956680514020189795025983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20871258816215357813610485 1956680514020189795025983)
  ·
    refine ⟨2935020771030284692538975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1956680514020189795025983 2935020771030284692538975)
    ·
      refine ⟨4402531156545427038808463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2935020771030284692538975 4402531156545427038808463)
      ·
        refine ⟨6603796734818140558212695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4402531156545427038808463 6603796734818140558212695)
        ·
          refine ⟨9905695102227210837319043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6603796734818140558212695 9905695102227210837319043)
          ·
            refine ⟨14858542653340816255978565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9905695102227210837319043 14858542653340816255978565)
            ·
              refine ⟨2785976747501403047995981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14858542653340816255978565 2785976747501403047995981)
              ·
                refine ⟨1044741280313026142998493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2785976747501403047995981 1044741280313026142998493)
                ·
                  refine ⟨391777980117384803624435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1044741280313026142998493 391777980117384803624435)
                  ·
                    rfl

theorem cell20_858358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 4, 3, 3].length) (baseStart_858358 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_858358 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_858358 prefixEnd_858358 := by exact prefixLift 858358
  have htrace : WordTrace (prefixWord ++ tailWord_858358) baseStart_858358 baseEnd_858358 := by
    simpa [prefixWord, tailWord_858358, baseEnd_858358] using wordTrace_append hprefix tailTrace_858358
  have hstable : (prefixWord ++ tailWord_858358).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_858358).length < 2 ^ (prefixWord ++ tailWord_858358).sum := by decide
  have hdescent : baseEnd_858358 < baseStart_858358 := by decide
  rcases family_descends (prefixWord ++ tailWord_858358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_858382 : List Nat := [4, 1, 1, 2, 1, 2, 4, 3, 2]
def baseStart_858382 : Nat := 118140960795 + 858382 * 2 ^ 59
def prefixEnd_858382 : Nat := 4983230072969 + 3 ^ 40 * 858382 * 2
def baseEnd_858382 : Nat := 391788934371347386824337

theorem tailTrace_858382 : CollatzResearch.WordTrace tailWord_858382 prefixEnd_858382 391788934371347386824337 := by
  unfold tailWord_858382
  simp only [CollatzResearch.WordTrace]
  refine ⟨3913470447029511102411175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20871842384157392546192933 3913470447029511102411175)
  ·
    refine ⟨5870205670544266653616763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3913470447029511102411175 5870205670544266653616763)
    ·
      refine ⟨8805308505816399980425145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5870205670544266653616763 8805308505816399980425145)
      ·
        refine ⟨6603981379362299985318859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8805308505816399980425145 6603981379362299985318859)
        ·
          refine ⟨9905972069043449977978289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6603981379362299985318859 9905972069043449977978289)
          ·
            refine ⟨7429479051782587483483717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9905972069043449977978289 7429479051782587483483717)
            ·
              refine ⟨1393027322209235153153197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7429479051782587483483717 1393027322209235153153197)
              ·
                refine ⟨522385245828463182432449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1393027322209235153153197 522385245828463182432449)
                ·
                  refine ⟨391788934371347386824337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 522385245828463182432449 391788934371347386824337)
                  ·
                    rfl

theorem cell20_858382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 4, 3, 2].length) (baseStart_858382 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_858382 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_858382 prefixEnd_858382 := by exact prefixLift 858382
  have htrace : WordTrace (prefixWord ++ tailWord_858382) baseStart_858382 baseEnd_858382 := by
    simpa [prefixWord, tailWord_858382, baseEnd_858382] using wordTrace_append hprefix tailTrace_858382
  have hstable : (prefixWord ++ tailWord_858382).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_858382).length < 2 ^ (prefixWord ++ tailWord_858382).sum := by decide
  have hdescent : baseEnd_858382 < baseStart_858382 := by decide
  rcases family_descends (prefixWord ++ tailWord_858382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_858403 : List Nat := [1, 1, 1, 4, 2, 2, 1, 6, 2]
def baseStart_858403 : Nat := 118140960795 + 858403 * 2 ^ 59
def prefixEnd_858403 : Nat := 4983230072969 + 3 ^ 40 * 858403 * 2
def baseEnd_858403 : Nat := 391798519343564647124251

theorem tailTrace_858403 : CollatzResearch.WordTrace tailWord_858403 prefixEnd_858403 391798519343564647124251 := by
  unfold tailWord_858403
  simp only [CollatzResearch.WordTrace]
  refine ⟨31308529509160009405803863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20872353006106672937202575 31308529509160009405803863)
  ·
    refine ⟨46962794263740014108705795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31308529509160009405803863 46962794263740014108705795)
    ·
      refine ⟨70444191395610021163058693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46962794263740014108705795 70444191395610021163058693)
      ·
        refine ⟨13208285886676878968073505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70444191395610021163058693 13208285886676878968073505)
        ·
          refine ⟨9906214415007659226055129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13208285886676878968073505 9906214415007659226055129)
          ·
            refine ⟨7429660811255744419541347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9906214415007659226055129 7429660811255744419541347)
            ·
              refine ⟨11144491216883616629312021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7429660811255744419541347 11144491216883616629312021)
              ·
                refine ⟨522398025791419529499001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 11144491216883616629312021 522398025791419529499001)
                ·
                  refine ⟨391798519343564647124251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 522398025791419529499001 391798519343564647124251)
                  ·
                    rfl

theorem cell20_858403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 6, 2].length) (baseStart_858403 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_858403 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_858403 prefixEnd_858403 := by exact prefixLift 858403
  have htrace : WordTrace (prefixWord ++ tailWord_858403) baseStart_858403 baseEnd_858403 := by
    simpa [prefixWord, tailWord_858403, baseEnd_858403] using wordTrace_append hprefix tailTrace_858403
  have hstable : (prefixWord ++ tailWord_858403).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_858403).length < 2 ^ (prefixWord ++ tailWord_858403).sum := by decide
  have hdescent : baseEnd_858403 < baseStart_858403 := by decide
  rcases family_descends (prefixWord ++ tailWord_858403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_858424 : List Nat := [2, 1, 2, 1, 3, 1, 4, 2, 4]
def baseStart_858424 : Nat := 118140960795 + 858424 * 2 ^ 59
def prefixEnd_858424 : Nat := 4983230072969 + 3 ^ 40 * 858424 * 2
def baseEnd_858424 : Nat := 391808104315781907424165

theorem tailTrace_858424 : CollatzResearch.WordTrace tailWord_858424 prefixEnd_858424 391808104315781907424165 := by
  unfold tailWord_858424
  simp only [CollatzResearch.WordTrace]
  refine ⟨15654647721041964996159163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20872863628055953328212217 15654647721041964996159163)
  ·
    refine ⟨23481971581562947494238745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15654647721041964996159163 23481971581562947494238745)
    ·
      refine ⟨17611478686172210620679059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23481971581562947494238745 17611478686172210620679059)
      ·
        refine ⟨26417218029258315931018589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17611478686172210620679059 26417218029258315931018589)
        ·
          refine ⟨9906456760971868474131971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26417218029258315931018589 9906456760971868474131971)
          ·
            refine ⟨14859685141457802711197957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9906456760971868474131971 14859685141457802711197957)
            ·
              refine ⟨2786190964023338008349617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14859685141457802711197957 2786190964023338008349617)
              ·
                refine ⟨2089643223017503506262213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2786190964023338008349617 2089643223017503506262213)
                ·
                  refine ⟨391808104315781907424165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2089643223017503506262213 391808104315781907424165)
                  ·
                    rfl

theorem cell20_858424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 4, 2, 4].length) (baseStart_858424 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_858424 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_858424 prefixEnd_858424 := by exact prefixLift 858424
  have htrace : WordTrace (prefixWord ++ tailWord_858424) baseStart_858424 baseEnd_858424 := by
    simpa [prefixWord, tailWord_858424, baseEnd_858424] using wordTrace_append hprefix tailTrace_858424
  have hstable : (prefixWord ++ tailWord_858424).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_858424).length < 2 ^ (prefixWord ++ tailWord_858424).sum := by decide
  have hdescent : baseEnd_858424 < baseStart_858424 := by decide
  rcases family_descends (prefixWord ++ tailWord_858424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_858431 : List Nat := [1, 1, 2, 2, 4, 1, 3, 6]
def baseStart_858431 : Nat := 118140960795 + 858431 * 2 ^ 59
def prefixEnd_858431 : Nat := 4983230072969 + 3 ^ 40 * 858431 * 2
def baseEnd_858431 : Nat := 130603766435506998063601

theorem tailTrace_858431 : CollatzResearch.WordTrace tailWord_858431 prefixEnd_858431 130603766435506998063601 := by
  unfold tailWord_858431
  simp only [CollatzResearch.WordTrace]
  refine ⟨31309550753058570187823147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20873033835372380125215431 31309550753058570187823147)
  ·
    refine ⟨46964326129587855281734721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31309550753058570187823147 46964326129587855281734721)
    ·
      refine ⟨35223244597190891461301041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46964326129587855281734721 35223244597190891461301041)
      ·
        refine ⟨26417433447893168595975781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35223244597190891461301041 26417433447893168595975781)
        ·
          refine ⟨4953268771479969111745459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26417433447893168595975781 4953268771479969111745459)
          ·
            refine ⟨7429903157219953667618189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4953268771479969111745459 7429903157219953667618189)
            ·
              refine ⟨2786213683957482625356821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7429903157219953667618189 2786213683957482625356821)
              ·
                refine ⟨130603766435506998063601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2786213683957482625356821 130603766435506998063601)
                ·
                  rfl

theorem cell20_858431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 3, 6].length) (baseStart_858431 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_858431 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_858431 prefixEnd_858431 := by exact prefixLift 858431
  have htrace : WordTrace (prefixWord ++ tailWord_858431) baseStart_858431 baseEnd_858431 := by
    simpa [prefixWord, tailWord_858431, baseEnd_858431] using wordTrace_append hprefix tailTrace_858431
  have hstable : (prefixWord ++ tailWord_858431).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_858431).length < 2 ^ (prefixWord ++ tailWord_858431).sum := by decide
  have hdescent : baseEnd_858431 < baseStart_858431 := by decide
  rcases family_descends (prefixWord ++ tailWord_858431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_858455 : List Nat := [1, 1, 3, 2, 3, 1, 2, 4, 3]
def baseStart_858455 : Nat := 118140960795 + 858455 * 2 ^ 59
def prefixEnd_858455 : Nat := 4983230072969 + 3 ^ 40 * 858455 * 2
def baseEnd_858455 : Nat := 391822253560483577390705

theorem tailTrace_858455 : CollatzResearch.WordTrace tailWord_858455 prefixEnd_858455 391822253560483577390705 := by
  unfold tailWord_858455
  simp only [CollatzResearch.WordTrace]
  refine ⟨31310426104971622286696819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20873617403314414857797879 31310426104971622286696819)
  ·
    refine ⟨46965639157457433430045229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31310426104971622286696819 46965639157457433430045229)
    ·
      refine ⟨17612114684046537536266961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46965639157457433430045229 17612114684046537536266961)
      ·
        refine ⟨13209086013034903152200221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17612114684046537536266961 13209086013034903152200221)
        ·
          refine ⟨4953407254888088682075083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13209086013034903152200221 4953407254888088682075083)
          ·
            refine ⟨7430110882332133023112625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4953407254888088682075083 7430110882332133023112625)
            ·
              refine ⟨5572583161749099767334469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7430110882332133023112625 5572583161749099767334469)
              ·
                refine ⟨1044859342827956206375213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5572583161749099767334469 1044859342827956206375213)
                ·
                  refine ⟨391822253560483577390705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1044859342827956206375213 391822253560483577390705)
                  ·
                    rfl

theorem cell20_858455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 4, 3].length) (baseStart_858455 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_858455 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_858455 prefixEnd_858455 := by exact prefixLift 858455
  have htrace : WordTrace (prefixWord ++ tailWord_858455) baseStart_858455 baseEnd_858455 := by
    simpa [prefixWord, tailWord_858455, baseEnd_858455] using wordTrace_append hprefix tailTrace_858455
  have hstable : (prefixWord ++ tailWord_858455).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_858455).length < 2 ^ (prefixWord ++ tailWord_858455).sum := by decide
  have hdescent : baseEnd_858455 < baseStart_858455 := by decide
  rcases family_descends (prefixWord ++ tailWord_858455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_858469 : List Nat := [1, 3, 1, 3, 1, 3, 1, 7]
def baseStart_858469 : Nat := 118140960795 + 858469 * 2 ^ 59
def prefixEnd_858469 : Nat := 4983230072969 + 3 ^ 40 * 858469 * 2
def baseEnd_858469 : Nat := 130609547847320583641327

theorem tailTrace_858469 : CollatzResearch.WordTrace tailWord_858469 prefixEnd_858469 130609547847320583641327 := by
  unfold tailWord_858469
  simp only [CollatzResearch.WordTrace]
  refine ⟨31310936726920902677706461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20873957817947268451804307 31310936726920902677706461)
  ·
    refine ⟨11741601272595338504139923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31310936726920902677706461 11741601272595338504139923)
    ·
      refine ⟨17612401908893007756209885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11741601272595338504139923 17612401908893007756209885)
      ·
        refine ⟨6604650715834877908578707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17612401908893007756209885 6604650715834877908578707)
        ·
          refine ⟨9906976073752316862868061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6604650715834877908578707 9906976073752316862868061)
          ·
            refine ⟨3715116027657118823575523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9906976073752316862868061 3715116027657118823575523)
            ·
              refine ⟨5572674041485678235363285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3715116027657118823575523 5572674041485678235363285)
              ·
                refine ⟨130609547847320583641327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5572674041485678235363285 130609547847320583641327)
                ·
                  rfl

theorem cell20_858469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 7].length) (baseStart_858469 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_858469 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_858469 prefixEnd_858469 := by exact prefixLift 858469
  have htrace : WordTrace (prefixWord ++ tailWord_858469) baseStart_858469 baseEnd_858469 := by
    simpa [prefixWord, tailWord_858469, baseEnd_858469] using wordTrace_append hprefix tailTrace_858469
  have hstable : (prefixWord ++ tailWord_858469).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_858469).length < 2 ^ (prefixWord ++ tailWord_858469).sum := by decide
  have hdescent : baseEnd_858469 < baseStart_858469 := by decide
  rcases family_descends (prefixWord ++ tailWord_858469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_858472 : List Nat := [2, 1, 4, 2, 2, 2, 1, 3, 3]
def baseStart_858472 : Nat := 118140960795 + 858472 * 2 ^ 59
def prefixEnd_858472 : Nat := 4983230072969 + 3 ^ 40 * 858472 * 2
def baseEnd_858472 : Nat := 391830012823707073823969

theorem tailTrace_858472 : CollatzResearch.WordTrace tailWord_858472 prefixEnd_858472 391830012823707073823969 := by
  unfold tailWord_858472
  simp only [CollatzResearch.WordTrace]
  refine ⟨15655523072955017095032835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20874030763940022793377113 15655523072955017095032835)
  ·
    refine ⟨23483284609432525642549253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15655523072955017095032835 23483284609432525642549253)
    ·
      refine ⟨4403115864268598557977985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23483284609432525642549253 4403115864268598557977985)
      ·
        refine ⟨3302336898201448918483489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4403115864268598557977985 3302336898201448918483489)
        ·
          refine ⟨2476752673651086688862617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3302336898201448918483489 2476752673651086688862617)
          ·
            refine ⟨1857564505238315016646963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2476752673651086688862617 1857564505238315016646963)
            ·
              refine ⟨2786346757857472524970445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1857564505238315016646963 2786346757857472524970445)
              ·
                refine ⟨1044880034196552196863917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2786346757857472524970445 1044880034196552196863917)
                ·
                  refine ⟨391830012823707073823969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1044880034196552196863917 391830012823707073823969)
                  ·
                    rfl

theorem cell20_858472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 1, 3, 3].length) (baseStart_858472 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_858472 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_858472 prefixEnd_858472 := by exact prefixLift 858472
  have htrace : WordTrace (prefixWord ++ tailWord_858472) baseStart_858472 baseEnd_858472 := by
    simpa [prefixWord, tailWord_858472, baseEnd_858472] using wordTrace_append hprefix tailTrace_858472
  have hstable : (prefixWord ++ tailWord_858472).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_858472).length < 2 ^ (prefixWord ++ tailWord_858472).sum := by decide
  have hdescent : baseEnd_858472 < baseStart_858472 := by decide
  rcases family_descends (prefixWord ++ tailWord_858472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_858510 : List Nat := [4, 1, 1, 4, 1, 1, 1, 4, 3]
def baseStart_858510 : Nat := 118140960795 + 858510 * 2 ^ 59
def prefixEnd_858510 : Nat := 4983230072969 + 3 ^ 40 * 858510 * 2
def baseEnd_858510 : Nat := 391847357059147830557147

theorem tailTrace_858510 : CollatzResearch.WordTrace tailWord_858510 prefixEnd_858510 391847357059147830557147 := by
  unfold tailWord_858510
  simp only [CollatzResearch.WordTrace]
  refine ⟨3914054014971545834993623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20874954746514911119965989 3914054014971545834993623)
  ·
    refine ⟨5871081022457318752490435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3914054014971545834993623 5871081022457318752490435)
    ·
      refine ⟨8806621533685978128735653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5871081022457318752490435 8806621533685978128735653)
      ·
        refine ⟨1651241537566120899137935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8806621533685978128735653 1651241537566120899137935)
        ·
          refine ⟨2476862306349181348706903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1651241537566120899137935 2476862306349181348706903)
          ·
            refine ⟨3715293459523772023060355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2476862306349181348706903 3715293459523772023060355)
            ·
              refine ⟨5572940189285658034590533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3715293459523772023060355 5572940189285658034590533)
              ·
                refine ⟨1044926285491060881485725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5572940189285658034590533 1044926285491060881485725)
                ·
                  refine ⟨391847357059147830557147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1044926285491060881485725 391847357059147830557147)
                  ·
                    rfl

theorem cell20_858510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 4, 3].length) (baseStart_858510 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_858510 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_858510 prefixEnd_858510 := by exact prefixLift 858510
  have htrace : WordTrace (prefixWord ++ tailWord_858510) baseStart_858510 baseEnd_858510 := by
    simpa [prefixWord, tailWord_858510, baseEnd_858510] using wordTrace_append hprefix tailTrace_858510
  have hstable : (prefixWord ++ tailWord_858510).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_858510).length < 2 ^ (prefixWord ++ tailWord_858510).sum := by decide
  have hdescent : baseEnd_858510 < baseStart_858510 := by decide
  rcases family_descends (prefixWord ++ tailWord_858510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_858531 : List Nat := [1, 1, 1, 4, 1, 4, 2, 3, 3]
def baseStart_858531 : Nat := 118140960795 + 858531 * 2 ^ 59
def prefixEnd_858531 : Nat := 4983230072969 + 3 ^ 40 * 858531 * 2
def baseEnd_858531 : Nat := 391856942031365090857061

theorem tailTrace_858531 : CollatzResearch.WordTrace tailWord_858531 prefixEnd_858531 391856942031365090857061 := by
  unfold tailWord_858531
  simp only [CollatzResearch.WordTrace]
  refine ⟨31313198052696287266463447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20875465368464191510975631 31313198052696287266463447)
  ·
    refine ⟨46969797079044430899695171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31313198052696287266463447 46969797079044430899695171)
    ·
      refine ⟨70454695618566646349542757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46969797079044430899695171 70454695618566646349542757)
      ·
        refine ⟨13210255428481246190539267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70454695618566646349542757 13210255428481246190539267)
        ·
          refine ⟨19815383142721869285808901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13210255428481246190539267 19815383142721869285808901)
          ·
            refine ⟨3715384339260350491089169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19815383142721869285808901 3715384339260350491089169)
            ·
              refine ⟨2786538254445262868316877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3715384339260350491089169 2786538254445262868316877)
              ·
                refine ⟨1044951845416973575618829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2786538254445262868316877 1044951845416973575618829)
                ·
                  refine ⟨391856942031365090857061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1044951845416973575618829 391856942031365090857061)
                  ·
                    rfl

theorem cell20_858531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 2, 3, 3].length) (baseStart_858531 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_858531 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_858531 prefixEnd_858531 := by exact prefixLift 858531
  have htrace : WordTrace (prefixWord ++ tailWord_858531) baseStart_858531 baseEnd_858531 := by
    simpa [prefixWord, tailWord_858531, baseEnd_858531] using wordTrace_append hprefix tailTrace_858531
  have hstable : (prefixWord ++ tailWord_858531).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_858531).length < 2 ^ (prefixWord ++ tailWord_858531).sum := by decide
  have hdescent : baseEnd_858531 < baseStart_858531 := by decide
  rcases family_descends (prefixWord ++ tailWord_858531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_858552 : List Nat := [2, 1, 2, 1, 2, 2, 1, 4, 5]
def baseStart_858552 : Nat := 118140960795 + 858552 * 2 ^ 59
def prefixEnd_858552 : Nat := 4983230072969 + 3 ^ 40 * 858552 * 2
def baseEnd_858552 : Nat := 391866527003582351156975

theorem tailTrace_858552 : CollatzResearch.WordTrace tailWord_858552 prefixEnd_858552 391866527003582351156975 := by
  unfold tailWord_858552
  simp only [CollatzResearch.WordTrace]
  refine ⟨15656981992810103926488955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20875975990413471901985273 15656981992810103926488955)
  ·
    refine ⟨23485472989215155889733433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15656981992810103926488955 23485472989215155889733433)
    ·
      refine ⟨17614104741911366917300075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23485472989215155889733433 17614104741911366917300075)
      ·
        refine ⟨26421157112867050375950113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17614104741911366917300075 26421157112867050375950113)
        ·
          refine ⟨19815867834650287781962585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26421157112867050375950113 19815867834650287781962585)
          ·
            refine ⟨14861900875987715836471939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19815867834650287781962585 14861900875987715836471939)
            ·
              refine ⟨22292851313981573754707909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14861900875987715836471939 22292851313981573754707909)
              ·
                refine ⟨4179909621371545079007733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22292851313981573754707909 4179909621371545079007733)
                ·
                  refine ⟨391866527003582351156975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4179909621371545079007733 391866527003582351156975)
                  ·
                    rfl

theorem cell20_858552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 4, 5].length) (baseStart_858552 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_858552 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_858552 prefixEnd_858552 := by exact prefixLift 858552
  have htrace : WordTrace (prefixWord ++ tailWord_858552) baseStart_858552 baseEnd_858552 := by
    simpa [prefixWord, tailWord_858552, baseEnd_858552] using wordTrace_append hprefix tailTrace_858552
  have hstable : (prefixWord ++ tailWord_858552).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_858552).length < 2 ^ (prefixWord ++ tailWord_858552).sum := by decide
  have hdescent : baseEnd_858552 < baseStart_858552 := by decide
  rcases family_descends (prefixWord ++ tailWord_858552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_858561 : List Nat := [1, 2, 7, 1, 1, 2, 1, 2, 3]
def baseStart_858561 : Nat := 118140960795 + 858561 * 2 ^ 59
def prefixEnd_858561 : Nat := 4983230072969 + 3 ^ 40 * 858561 * 2
def baseEnd_858561 : Nat := 391870634848818319856939

theorem tailTrace_858561 : CollatzResearch.WordTrace tailWord_858561 prefixEnd_858561 391870634848818319856939 := by
  unfold tailWord_858561
  simp only [CollatzResearch.WordTrace]
  refine ⟨31314292242587602390055537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20876194828391734926703691 31314292242587602390055537)
  ·
    refine ⟨23485719181940701792541653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31314292242587602390055537 23485719181940701792541653)
    ·
      refine ⟨550446543326735198262695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 23485719181940701792541653 550446543326735198262695)
      ·
        refine ⟨825669814990102797394043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 550446543326735198262695 825669814990102797394043)
        ·
          refine ⟨1238504722485154196091065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 825669814990102797394043 1238504722485154196091065)
          ·
            refine ⟨928878541863865647068299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1238504722485154196091065 928878541863865647068299)
            ·
              refine ⟨1393317812795798470602449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 928878541863865647068299 1393317812795798470602449)
              ·
                refine ⟨1044988359596848852951837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1393317812795798470602449 1044988359596848852951837)
                ·
                  refine ⟨391870634848818319856939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1044988359596848852951837 391870634848818319856939)
                  ·
                    rfl

theorem cell20_858561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 1, 2, 3].length) (baseStart_858561 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_858561 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_858561 prefixEnd_858561 := by exact prefixLift 858561
  have htrace : WordTrace (prefixWord ++ tailWord_858561) baseStart_858561 baseEnd_858561 := by
    simpa [prefixWord, tailWord_858561, baseEnd_858561] using wordTrace_append hprefix tailTrace_858561
  have hstable : (prefixWord ++ tailWord_858561).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_858561).length < 2 ^ (prefixWord ++ tailWord_858561).sum := by decide
  have hdescent : baseEnd_858561 < baseStart_858561 := by decide
  rcases family_descends (prefixWord ++ tailWord_858561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_858569 : List Nat := [1, 2, 1, 1, 2, 1, 7, 2, 3]
def baseStart_858569 : Nat := 118140960795 + 858569 * 2 ^ 59
def prefixEnd_858569 : Nat := 4983230072969 + 3 ^ 40 * 858569 * 2
def baseEnd_858569 : Nat := 391874286266805847590239

theorem tailTrace_858569 : CollatzResearch.WordTrace tailWord_858569 prefixEnd_858569 391874286266805847590239 := by
  unfold tailWord_858569
  simp only [CollatzResearch.WordTrace]
  refine ⟨31314584026558619756346761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20876389351039079837564507 31314584026558619756346761)
  ·
    refine ⟨23485938019918964817260071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31314584026558619756346761 23485938019918964817260071)
    ·
      refine ⟨35228907029878447225890107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23485938019918964817260071 35228907029878447225890107)
      ·
        refine ⟨52843360544817670838835161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35228907029878447225890107 52843360544817670838835161)
        ·
          refine ⟨39632520408613253129126371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52843360544817670838835161 39632520408613253129126371)
          ·
            refine ⟨59448780612919879693689557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39632520408613253129126371 59448780612919879693689557)
            ·
              refine ⟨1393330795615309680320849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 59448780612919879693689557 1393330795615309680320849)
              ·
                refine ⟨1044998096711482260240637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1393330795615309680320849 1044998096711482260240637)
                ·
                  refine ⟨391874286266805847590239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1044998096711482260240637 391874286266805847590239)
                  ·
                    rfl

theorem cell20_858569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 7, 2, 3].length) (baseStart_858569 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_858569 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_858569 prefixEnd_858569 := by exact prefixLift 858569
  have htrace : WordTrace (prefixWord ++ tailWord_858569) baseStart_858569 baseEnd_858569 := by
    simpa [prefixWord, tailWord_858569, baseEnd_858569] using wordTrace_append hprefix tailTrace_858569
  have hstable : (prefixWord ++ tailWord_858569).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_858569).length < 2 ^ (prefixWord ++ tailWord_858569).sum := by decide
  have hdescent : baseEnd_858569 < baseStart_858569 := by decide
  rcases family_descends (prefixWord ++ tailWord_858569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_858586 : List Nat := [3, 1, 1, 2, 3, 1, 5, 1, 3]
def baseStart_858586 : Nat := 118140960795 + 858586 * 2 ^ 59
def prefixEnd_858586 : Nat := 4983230072969 + 3 ^ 40 * 858586 * 2
def baseEnd_858586 : Nat := 391882045530029344023503

theorem tailTrace_858586 : CollatzResearch.WordTrace tailWord_858586 prefixEnd_858586 391882045530029344023503 := by
  unfold tailWord_858586
  simp only [CollatzResearch.WordTrace]
  refine ⟨7828801016874257914928903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20876802711664687773143741 7828801016874257914928903)
  ·
    refine ⟨11743201525311386872393355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7828801016874257914928903 11743201525311386872393355)
    ·
      refine ⟨17614802287967080308590033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11743201525311386872393355 17614802287967080308590033)
      ·
        refine ⟨13211101715975310231442525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17614802287967080308590033 13211101715975310231442525)
        ·
          refine ⟨4954163143490741336790947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13211101715975310231442525 4954163143490741336790947)
          ·
            refine ⟨7431244715236112005186421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4954163143490741336790947 7431244715236112005186421)
            ·
              refine ⟨696679192053385500486227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7431244715236112005186421 696679192053385500486227)
              ·
                refine ⟨1045018788080078250729341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 696679192053385500486227 1045018788080078250729341)
                ·
                  refine ⟨391882045530029344023503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1045018788080078250729341 391882045530029344023503)
                  ·
                    rfl

theorem cell20_858586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 5, 1, 3].length) (baseStart_858586 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_858586 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_858586 prefixEnd_858586 := by exact prefixLift 858586
  have htrace : WordTrace (prefixWord ++ tailWord_858586) baseStart_858586 baseEnd_858586 := by
    simpa [prefixWord, tailWord_858586, baseEnd_858586] using wordTrace_append hprefix tailTrace_858586
  have hstable : (prefixWord ++ tailWord_858586).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_858586).length < 2 ^ (prefixWord ++ tailWord_858586).sum := by decide
  have hdescent : baseEnd_858586 < baseStart_858586 := by decide
  rcases family_descends (prefixWord ++ tailWord_858586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_858600 : List Nat := [2, 1, 4, 1, 1, 3, 4, 4]
def baseStart_858600 : Nat := 118140960795 + 858600 * 2 ^ 59
def prefixEnd_858600 : Nat := 4983230072969 + 3 ^ 40 * 858600 * 2
def baseEnd_858600 : Nat := 130629478503835839185593

theorem tailTrace_858600 : CollatzResearch.WordTrace tailWord_858600 prefixEnd_858600 130629478503835839185593 := by
  unfold tailWord_858600
  simp only [CollatzResearch.WordTrace]
  refine ⟨15657857344723156025362627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20877143126297541367150169 15657857344723156025362627)
  ·
    refine ⟨23486786017084734038043941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15657857344723156025362627 23486786017084734038043941)
    ·
      refine ⟨4403772378203387632133239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23486786017084734038043941 4403772378203387632133239)
      ·
        refine ⟨6605658567305081448199859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4403772378203387632133239 6605658567305081448199859)
        ·
          refine ⟨9908487850957622172299789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6605658567305081448199859 9908487850957622172299789)
          ·
            refine ⟨3715682944109108314612421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9908487850957622172299789 3715682944109108314612421)
            ·
              refine ⟨696690552020457808989829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3715682944109108314612421 696690552020457808989829)
              ·
                refine ⟨130629478503835839185593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 696690552020457808989829 130629478503835839185593)
                ·
                  rfl

theorem cell20_858600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 4, 4].length) (baseStart_858600 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_858600 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_858600 prefixEnd_858600 := by exact prefixLift 858600
  have htrace : WordTrace (prefixWord ++ tailWord_858600) baseStart_858600 baseEnd_858600 := by
    simpa [prefixWord, tailWord_858600, baseEnd_858600] using wordTrace_append hprefix tailTrace_858600
  have hstable : (prefixWord ++ tailWord_858600).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_858600).length < 2 ^ (prefixWord ++ tailWord_858600).sum := by decide
  have hdescent : baseEnd_858600 < baseStart_858600 := by decide
  rcases family_descends (prefixWord ++ tailWord_858600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_858637 : List Nat := [1, 7, 1, 1, 1, 3, 2, 1, 3]
def baseStart_858637 : Nat := 118140960795 + 858637 * 2 ^ 59
def prefixEnd_858637 : Nat := 4983230072969 + 3 ^ 40 * 858637 * 2
def baseEnd_858637 : Nat := 391905323319699833323295

theorem tailTrace_858637 : CollatzResearch.WordTrace tailWord_858637 prefixEnd_858637 391905323319699833323295 := by
  unfold tailWord_858637
  simp only [CollatzResearch.WordTrace]
  refine ⟨31317064190312267369822165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20878042793541511579881443 31317064190312267369822165)
  ·
    refine ⟨733993691960443766480207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 31317064190312267369822165 733993691960443766480207)
    ·
      refine ⟨1100990537940665649720311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 733993691960443766480207 1100990537940665649720311)
      ·
        refine ⟨1651485806910998474580467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1100990537940665649720311 1651485806910998474580467)
        ·
          refine ⟨2477228710366497711870701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1651485806910998474580467 2477228710366497711870701)
          ·
            refine ⟨928960766387436641951513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2477228710366497711870701 928960766387436641951513)
            ·
              refine ⟨696720574790577481463635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 928960766387436641951513 696720574790577481463635)
              ·
                refine ⟨1045080862185866222195453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 696720574790577481463635 1045080862185866222195453)
                ·
                  refine ⟨391905323319699833323295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1045080862185866222195453 391905323319699833323295)
                  ·
                    rfl

theorem cell20_858637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 2, 1, 3].length) (baseStart_858637 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_858637 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_858637 prefixEnd_858637 := by exact prefixLift 858637
  have htrace : WordTrace (prefixWord ++ tailWord_858637) baseStart_858637 baseEnd_858637 := by
    simpa [prefixWord, tailWord_858637, baseEnd_858637] using wordTrace_append hprefix tailTrace_858637
  have hstable : (prefixWord ++ tailWord_858637).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_858637).length < 2 ^ (prefixWord ++ tailWord_858637).sum := by decide
  have hdescent : baseEnd_858637 < baseStart_858637 := by decide
  rcases family_descends (prefixWord ++ tailWord_858637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_858638 : List Nat := [4, 1, 1, 2, 3, 2, 2, 5]
def baseStart_858638 : Nat := 118140960795 + 858638 * 2 ^ 59
def prefixEnd_858638 : Nat := 4983230072969 + 3 ^ 40 * 858638 * 2
def baseEnd_858638 : Nat := 130635259915649424763319

theorem tailTrace_858638 : CollatzResearch.WordTrace tailWord_858638 prefixEnd_858638 130635259915649424763319 := by
  unfold tailWord_858638
  simp only [CollatzResearch.WordTrace]
  refine ⟨3914637582913580567576071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20878067108872429693739045 3914637582913580567576071)
  ·
    refine ⟨5871956374370370851364107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3914637582913580567576071 5871956374370370851364107)
    ·
      refine ⟨8807934561555556277046161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5871956374370370851364107 8807934561555556277046161)
      ·
        refine ⟨6605950921166667207784621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8807934561555556277046161 6605950921166667207784621)
        ·
          refine ⟨2477231595437500202919233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6605950921166667207784621 2477231595437500202919233)
          ·
            refine ⟨1857923696578125152189425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2477231595437500202919233 1857923696578125152189425)
            ·
              refine ⟨1393442772433593864142069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1857923696578125152189425 1393442772433593864142069)
              ·
                refine ⟨130635259915649424763319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1393442772433593864142069 130635259915649424763319)
                ·
                  rfl

theorem cell20_858638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 2, 5].length) (baseStart_858638 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_858638 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_858638 prefixEnd_858638 := by exact prefixLift 858638
  have htrace : WordTrace (prefixWord ++ tailWord_858638) baseStart_858638 baseEnd_858638 := by
    simpa [prefixWord, tailWord_858638, baseEnd_858638] using wordTrace_append hprefix tailTrace_858638
  have hstable : (prefixWord ++ tailWord_858638).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_858638).length < 2 ^ (prefixWord ++ tailWord_858638).sum := by decide
  have hdescent : baseEnd_858638 < baseStart_858638 := by decide
  rcases family_descends (prefixWord ++ tailWord_858638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_858645 : List Nat := [1, 3, 2, 1, 3, 1, 3, 3, 3]
def baseStart_858645 : Nat := 118140960795 + 858645 * 2 ^ 59
def prefixEnd_858645 : Nat := 4983230072969 + 3 ^ 40 * 858645 * 2
def baseEnd_858645 : Nat := 391908974737687361056595

theorem tailTrace_858645 : CollatzResearch.WordTrace tailWord_858645 prefixEnd_858645 391908974737687361056595 := by
  unfold tailWord_858645
  simp only [CollatzResearch.WordTrace]
  refine ⟨31317355974283284736113389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20878237316188856490742259 31317355974283284736113389)
  ·
    refine ⟨11744008490356231776042521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31317355974283284736113389 11744008490356231776042521)
    ·
      refine ⟨8808006367767173832031891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11744008490356231776042521 8808006367767173832031891)
      ·
        refine ⟨13212009551650760748047837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8808006367767173832031891 13212009551650760748047837)
        ·
          refine ⟨4954503581869035280517939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13212009551650760748047837 4954503581869035280517939)
          ·
            refine ⟨7431755372803552920776909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4954503581869035280517939 7431755372803552920776909)
            ·
              refine ⟨2786908264801332345291341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7431755372803552920776909 2786908264801332345291341)
              ·
                refine ⟨1045090599300499629484253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2786908264801332345291341 1045090599300499629484253)
                ·
                  refine ⟨391908974737687361056595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1045090599300499629484253 391908974737687361056595)
                  ·
                    rfl

theorem cell20_858645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 3, 3, 3].length) (baseStart_858645 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_858645 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_858645 prefixEnd_858645 := by exact prefixLift 858645
  have htrace : WordTrace (prefixWord ++ tailWord_858645) baseStart_858645 baseEnd_858645 := by
    simpa [prefixWord, tailWord_858645, baseEnd_858645] using wordTrace_append hprefix tailTrace_858645
  have hstable : (prefixWord ++ tailWord_858645).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_858645).length < 2 ^ (prefixWord ++ tailWord_858645).sum := by decide
  have hdescent : baseEnd_858645 < baseStart_858645 := by decide
  rcases family_descends (prefixWord ++ tailWord_858645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_858659 : List Nat := [1, 1, 1, 4, 4, 1, 2, 6]
def baseStart_858659 : Nat := 118140960795 + 858659 * 2 ^ 59
def prefixEnd_858659 : Nat := 4983230072969 + 3 ^ 40 * 858659 * 2
def baseEnd_858659 : Nat := 130638454906388511529957

theorem tailTrace_858659 : CollatzResearch.WordTrace tailWord_858659 prefixEnd_858659 130638454906388511529957 := by
  unfold tailWord_858659
  simp only [CollatzResearch.WordTrace]
  refine ⟨31317866596232565127123031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20878577730821710084748687 31317866596232565127123031)
  ·
    refine ⟨46976799894348847690684547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31317866596232565127123031 46976799894348847690684547)
    ·
      refine ⟨70465199841523271536026821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46976799894348847690684547 70465199841523271536026821)
      ·
        refine ⟨13212224970285613413005029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70465199841523271536026821 13212224970285613413005029)
        ·
          refine ⟨2477292181928552514938443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13212224970285613413005029 2477292181928552514938443)
          ·
            refine ⟨3715938272892828772407665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2477292181928552514938443 3715938272892828772407665)
            ·
              refine ⟨2786953704669621579305749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3715938272892828772407665 2786953704669621579305749)
              ·
                refine ⟨130638454906388511529957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2786953704669621579305749 130638454906388511529957)
                ·
                  rfl

theorem cell20_858659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 2, 6].length) (baseStart_858659 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_858659 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_858659 prefixEnd_858659 := by exact prefixLift 858659
  have htrace : WordTrace (prefixWord ++ tailWord_858659) baseStart_858659 baseEnd_858659 := by
    simpa [prefixWord, tailWord_858659, baseEnd_858659] using wordTrace_append hprefix tailTrace_858659
  have hstable : (prefixWord ++ tailWord_858659).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_858659).length < 2 ^ (prefixWord ++ tailWord_858659).sum := by decide
  have hdescent : baseEnd_858659 < baseStart_858659 := by decide
  rcases family_descends (prefixWord ++ tailWord_858659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_858676 : List Nat := [2, 5, 1, 3, 9]
def baseStart_858676 : Nat := 118140960795 + 858676 * 2 ^ 59
def prefixEnd_858676 : Nat := 4983230072969 + 3 ^ 40 * 858676 * 2
def baseEnd_858676 : Nat := 4838557086202333716335

theorem tailTrace_858676 : CollatzResearch.WordTrace tailWord_858676 prefixEnd_858676 4838557086202333716335 := by
  unfold tailWord_858676
  simp only [CollatzResearch.WordTrace]
  refine ⟨15659243318585488515245941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20878991091447318020327921 15659243318585488515245941)
  ·
    refine ⟨1468054061117389548304307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15659243318585488515245941 1468054061117389548304307)
    ·
      refine ⟨2202081091676084322456461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1468054061117389548304307 2202081091676084322456461)
      ·
        refine ⟨825780409378531620921173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2202081091676084322456461 825780409378531620921173)
        ·
          refine ⟨4838557086202333716335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 825780409378531620921173 4838557086202333716335)
          ·
            rfl

theorem cell20_858676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 9].length) (baseStart_858676 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_858676 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_858676 prefixEnd_858676 := by exact prefixLift 858676
  have htrace : WordTrace (prefixWord ++ tailWord_858676) baseStart_858676 baseEnd_858676 := by
    simpa [prefixWord, tailWord_858676, baseEnd_858676] using wordTrace_append hprefix tailTrace_858676
  have hstable : (prefixWord ++ tailWord_858676).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_858676).length < 2 ^ (prefixWord ++ tailWord_858676).sum := by decide
  have hdescent : baseEnd_858676 < baseStart_858676 := by decide
  rcases family_descends (prefixWord ++ tailWord_858676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_858745 : List Nat := [1, 2, 1, 3, 3, 2, 2, 4, 2]
def baseStart_858745 : Nat := 118140960795 + 858745 * 2 ^ 59
def prefixEnd_858745 : Nat := 4983230072969 + 3 ^ 40 * 858745 * 2
def baseEnd_858745 : Nat := 391954617462531457722853

theorem tailTrace_858745 : CollatzResearch.WordTrace tailWord_858745 prefixEnd_858745 391954617462531457722853 := by
  unfold tailWord_858745
  simp only [CollatzResearch.WordTrace]
  refine ⟨31321003273921001814753689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20880668849280667876502459 31321003273921001814753689)
  ·
    refine ⟨23490752455440751361065267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31321003273921001814753689 23490752455440751361065267)
    ·
      refine ⟨35236128683161127041597901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23490752455440751361065267 35236128683161127041597901)
      ·
        refine ⟨13213548256185422640599213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35236128683161127041597901 13213548256185422640599213)
        ·
          refine ⟨4955080596069533490224705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13213548256185422640599213 4955080596069533490224705)
          ·
            refine ⟨3716310447052150117668529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4955080596069533490224705 3716310447052150117668529)
            ·
              refine ⟨2787232835289112588251397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3716310447052150117668529 2787232835289112588251397)
              ·
                refine ⟨522606156616708610297137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2787232835289112588251397 522606156616708610297137)
                ·
                  refine ⟨391954617462531457722853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 522606156616708610297137 391954617462531457722853)
                  ·
                    rfl

theorem cell20_858745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 2, 4, 2].length) (baseStart_858745 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_858745 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_858745 prefixEnd_858745 := by exact prefixLift 858745
  have htrace : WordTrace (prefixWord ++ tailWord_858745) baseStart_858745 baseEnd_858745 := by
    simpa [prefixWord, tailWord_858745, baseEnd_858745] using wordTrace_append hprefix tailTrace_858745
  have hstable : (prefixWord ++ tailWord_858745).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_858745).length < 2 ^ (prefixWord ++ tailWord_858745).sum := by decide
  have hdescent : baseEnd_858745 < baseStart_858745 := by decide
  rcases family_descends (prefixWord ++ tailWord_858745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_858766 : List Nat := [4, 1, 1, 3, 1, 1, 1, 4, 4]
def baseStart_858766 : Nat := 118140960795 + 858766 * 2 ^ 59
def prefixEnd_858766 : Nat := 4983230072969 + 3 ^ 40 * 858766 * 2
def baseEnd_858766 : Nat := 391964202434748718022767

theorem tailTrace_858766 : CollatzResearch.WordTrace tailWord_858766 prefixEnd_858766 391964202434748718022767 := by
  unfold tailWord_858766
  simp only [CollatzResearch.WordTrace]
  refine ⟨3915221150855615300158519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20881179471229948267512101 3915221150855615300158519)
  ·
    refine ⟨5872831726283422950237779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3915221150855615300158519 5872831726283422950237779)
    ·
      refine ⟨8809247589425134425356669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5872831726283422950237779 8809247589425134425356669)
      ·
        refine ⟨3303467846034425409508751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8809247589425134425356669 3303467846034425409508751)
        ·
          refine ⟨4955201769051638114263127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3303467846034425409508751 4955201769051638114263127)
          ·
            refine ⟨7432802653577457171394691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4955201769051638114263127 7432802653577457171394691)
            ·
              refine ⟨11149203980366185757092037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7432802653577457171394691 11149203980366185757092037)
              ·
                refine ⟨2090475746318659829454757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11149203980366185757092037 2090475746318659829454757)
                ·
                  refine ⟨391964202434748718022767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2090475746318659829454757 391964202434748718022767)
                  ·
                    rfl

theorem cell20_858766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 4, 4].length) (baseStart_858766 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_858766 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_858766 prefixEnd_858766 := by exact prefixLift 858766
  have htrace : WordTrace (prefixWord ++ tailWord_858766) baseStart_858766 baseEnd_858766 := by
    simpa [prefixWord, tailWord_858766, baseEnd_858766] using wordTrace_append hprefix tailTrace_858766
  have hstable : (prefixWord ++ tailWord_858766).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_858766).length < 2 ^ (prefixWord ++ tailWord_858766).sum := by decide
  have hdescent : baseEnd_858766 < baseStart_858766 := by decide
  rcases family_descends (prefixWord ++ tailWord_858766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_858797 : List Nat := [1, 5, 2, 1, 1, 2, 2, 1, 5]
def baseStart_858797 : Nat := 118140960795 + 858797 * 2 ^ 59
def prefixEnd_858797 : Nat := 4983230072969 + 3 ^ 40 * 858797 * 2
def baseEnd_858797 : Nat := 391978351679450387989307

theorem tailTrace_858797 : CollatzResearch.WordTrace tailWord_858797 prefixEnd_858797 391978351679450387989307 := by
  unfold tailWord_858797
  simp only [CollatzResearch.WordTrace]
  refine ⟨31322899869732614695646645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20881933246488409797097763 31322899869732614695646645)
  ·
    refine ⟨2936521862787432627716873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 31322899869732614695646645 2936521862787432627716873)
    ·
      refine ⟨2202391397090574470787655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2936521862787432627716873 2202391397090574470787655)
      ·
        refine ⟨3303587095635861706181483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2202391397090574470787655 3303587095635861706181483)
        ·
          refine ⟨4955380643453792559272225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3303587095635861706181483 4955380643453792559272225)
          ·
            refine ⟨3716535482590344419454169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4955380643453792559272225 3716535482590344419454169)
            ·
              refine ⟨2787401611942758314590627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3716535482590344419454169 2787401611942758314590627)
              ·
                refine ⟨4181102417914137471885941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2787401611942758314590627 4181102417914137471885941)
                ·
                  refine ⟨391978351679450387989307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4181102417914137471885941 391978351679450387989307)
                  ·
                    rfl

theorem cell20_858797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 2, 1, 5].length) (baseStart_858797 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_858797 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_858797 prefixEnd_858797 := by exact prefixLift 858797
  have htrace : WordTrace (prefixWord ++ tailWord_858797) baseStart_858797 baseEnd_858797 := by
    simpa [prefixWord, tailWord_858797, baseEnd_858797] using wordTrace_append hprefix tailTrace_858797
  have hstable : (prefixWord ++ tailWord_858797).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_858797).length < 2 ^ (prefixWord ++ tailWord_858797).sum := by decide
  have hdescent : baseEnd_858797 < baseStart_858797 := by decide
  rcases family_descends (prefixWord ++ tailWord_858797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_858866 : List Nat := [3, 2, 1, 3, 1, 4, 1, 5]
def baseStart_858866 : Nat := 118140960795 + 858866 * 2 ^ 59
def prefixEnd_858866 : Nat := 4983230072969 + 3 ^ 40 * 858866 * 2
def baseEnd_858866 : Nat := 130669948386530938229675

theorem tailTrace_858866 : CollatzResearch.WordTrace tailWord_858866 prefixEnd_858866 130669948386530938229675 := by
  unfold tailWord_858866
  simp only [CollatzResearch.WordTrace]
  refine ⟨7831354126620659869977113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20883611004321759653272301 7831354126620659869977113)
  ·
    refine ⟨5873515594965494902482835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7831354126620659869977113 5873515594965494902482835)
    ·
      refine ⟨8810273392448242353724253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5873515594965494902482835 8810273392448242353724253)
      ·
        refine ⟨3303852522168090882646595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8810273392448242353724253 3303852522168090882646595)
        ·
          refine ⟨4955778783252136323969893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3303852522168090882646595 4955778783252136323969893)
          ·
            refine ⟨929208521859775560744355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4955778783252136323969893 929208521859775560744355)
            ·
              refine ⟨1393812782789663341116533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 929208521859775560744355 1393812782789663341116533)
              ·
                refine ⟨130669948386530938229675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1393812782789663341116533 130669948386530938229675)
                ·
                  rfl

theorem cell20_858866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 1, 5].length) (baseStart_858866 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_858866 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_858866 prefixEnd_858866 := by exact prefixLift 858866
  have htrace : WordTrace (prefixWord ++ tailWord_858866) baseStart_858866 baseEnd_858866 := by
    simpa [prefixWord, tailWord_858866, baseEnd_858866] using wordTrace_append hprefix tailTrace_858866
  have hstable : (prefixWord ++ tailWord_858866).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_858866).length < 2 ^ (prefixWord ++ tailWord_858866).sum := by decide
  have hdescent : baseEnd_858866 < baseStart_858866 := by decide
  rcases family_descends (prefixWord ++ tailWord_858866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_858894 : List Nat := [4, 1, 1, 2, 1, 1, 1, 4, 5]
def baseStart_858894 : Nat := 118140960795 + 858894 * 2 ^ 59
def prefixEnd_858894 : Nat := 4983230072969 + 3 ^ 40 * 858894 * 2
def baseEnd_858894 : Nat := 392022625122549161755577

theorem tailTrace_858894 : CollatzResearch.WordTrace tailWord_858894 prefixEnd_858894 392022625122549161755577 := by
  unfold tailWord_858894
  simp only [CollatzResearch.WordTrace]
  refine ⟨3915804718797650032740967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20884291833587466841285157 3915804718797650032740967)
  ·
    refine ⟨5873707078196475049111451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3915804718797650032740967 5873707078196475049111451)
    ·
      refine ⟨8810560617294712573667177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5873707078196475049111451 8810560617294712573667177)
      ·
        refine ⟨6607920462971034430250383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8810560617294712573667177 6607920462971034430250383)
        ·
          refine ⟨9911880694456551645375575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6607920462971034430250383 9911880694456551645375575)
          ·
            refine ⟨14867821041684827468063363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9911880694456551645375575 14867821041684827468063363)
            ·
              refine ⟨22301731562527241202095045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14867821041684827468063363 22301731562527241202095045)
              ·
                refine ⟨4181574667973857725392821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22301731562527241202095045 4181574667973857725392821)
                ·
                  refine ⟨392022625122549161755577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4181574667973857725392821 392022625122549161755577)
                  ·
                    rfl

theorem cell20_858894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 4, 5].length) (baseStart_858894 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_858894 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_858894 prefixEnd_858894 := by exact prefixLift 858894
  have htrace : WordTrace (prefixWord ++ tailWord_858894) baseStart_858894 baseEnd_858894 := by
    simpa [prefixWord, tailWord_858894, baseEnd_858894] using wordTrace_append hprefix tailTrace_858894
  have hstable : (prefixWord ++ tailWord_858894).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_858894).length < 2 ^ (prefixWord ++ tailWord_858894).sum := by decide
  have hdescent : baseEnd_858894 < baseStart_858894 := by decide
  rcases family_descends (prefixWord ++ tailWord_858894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_858901 : List Nat := [1, 3, 2, 1, 2, 2, 1, 2, 6]
def baseStart_858901 : Nat := 118140960795 + 858901 * 2 ^ 59
def prefixEnd_858901 : Nat := 4983230072969 + 3 ^ 40 * 858901 * 2
def baseEnd_858901 : Nat := 392025820113288248522215

theorem tailTrace_858901 : CollatzResearch.WordTrace tailWord_858901 prefixEnd_858901 392025820113288248522215 := by
  unfold tailWord_858901
  simp only [CollatzResearch.WordTrace]
  refine ⟨31326693061355840457432557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20884462040903893638288371 31326693061355840457432557)
  ·
    refine ⟨11747509898008440171537209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31326693061355840457432557 11747509898008440171537209)
    ·
      refine ⟨8810632423506330128652907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11747509898008440171537209 8810632423506330128652907)
      ·
        refine ⟨13215948635259495192979361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8810632423506330128652907 13215948635259495192979361)
        ·
          refine ⟨9911961476444621394734521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13215948635259495192979361 9911961476444621394734521)
          ·
            refine ⟨7433971107333466046050891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9911961476444621394734521 7433971107333466046050891)
            ·
              refine ⟨11150956661000199069076337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7433971107333466046050891 11150956661000199069076337)
              ·
                refine ⟨8363217495750149301807253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11150956661000199069076337 8363217495750149301807253)
                ·
                  refine ⟨392025820113288248522215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8363217495750149301807253 392025820113288248522215)
                  ·
                    rfl

theorem cell20_858901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 2, 6].length) (baseStart_858901 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_858901 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_858901 prefixEnd_858901 := by exact prefixLift 858901
  have htrace : WordTrace (prefixWord ++ tailWord_858901) baseStart_858901 baseEnd_858901 := by
    simpa [prefixWord, tailWord_858901, baseEnd_858901] using wordTrace_append hprefix tailTrace_858901
  have hstable : (prefixWord ++ tailWord_858901).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_858901).length < 2 ^ (prefixWord ++ tailWord_858901).sum := by decide
  have hdescent : baseEnd_858901 < baseStart_858901 := by decide
  rcases family_descends (prefixWord ++ tailWord_858901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_858911 : List Nat := [1, 1, 2, 4, 2, 2, 3, 2, 3]
def baseStart_858911 : Nat := 118140960795 + 858911 * 2 ^ 59
def prefixEnd_858911 : Nat := 4983230072969 + 3 ^ 40 * 858911 * 2
def baseEnd_858911 : Nat := 392030384385772658188841

theorem tailTrace_858911 : CollatzResearch.WordTrace tailWord_858911 prefixEnd_858911 392030384385772658188841 := by
  unfold tailWord_858911
  simp only [CollatzResearch.WordTrace]
  refine ⟨31327057791319612165296587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20884705194213074776864391 31327057791319612165296587)
  ·
    refine ⟨46990586686979418247944881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31327057791319612165296587 46990586686979418247944881)
    ·
      refine ⟨35242940015234563685958661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46990586686979418247944881 35242940015234563685958661)
      ·
        refine ⟨6608051252856480691117249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35242940015234563685958661 6608051252856480691117249)
        ·
          refine ⟨4956038439642360518337937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6608051252856480691117249 4956038439642360518337937)
          ·
            refine ⟨3717028829731770388753453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4956038439642360518337937 3717028829731770388753453)
            ·
              refine ⟨1393885811149413895782545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3717028829731770388753453 1393885811149413895782545)
              ·
                refine ⟨1045414358362060421836909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1393885811149413895782545 1045414358362060421836909)
                ·
                  refine ⟨392030384385772658188841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1045414358362060421836909 392030384385772658188841)
                  ·
                    rfl

theorem cell20_858911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 3, 2, 3].length) (baseStart_858911 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_858911 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_858911 prefixEnd_858911 := by exact prefixLift 858911
  have htrace : WordTrace (prefixWord ++ tailWord_858911) baseStart_858911 baseEnd_858911 := by
    simpa [prefixWord, tailWord_858911, baseEnd_858911] using wordTrace_append hprefix tailTrace_858911
  have hstable : (prefixWord ++ tailWord_858911).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_858911).length < 2 ^ (prefixWord ++ tailWord_858911).sum := by decide
  have hdescent : baseEnd_858911 < baseStart_858911 := by decide
  rcases family_descends (prefixWord ++ tailWord_858911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_858942 : List Nat := [4, 2, 1, 2, 3, 1, 1, 6]
def baseStart_858942 : Nat := 118140960795 + 858942 * 2 ^ 59
def prefixEnd_858942 : Nat := 4983230072969 + 3 ^ 40 * 858942 * 2
def baseEnd_858942 : Nat := 130681511210158109385127

theorem tailTrace_858942 : CollatzResearch.WordTrace tailWord_858942 prefixEnd_858942 130681511210158109385127 := by
  unfold tailWord_858942
  simp only [CollatzResearch.WordTrace]
  refine ⟨3916023556775913057459385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20885458969471536306450053 3916023556775913057459385)
  ·
    refine ⟨2937017667581934793094539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3916023556775913057459385 2937017667581934793094539)
    ·
      refine ⟨4405526501372902189641809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2937017667581934793094539 4405526501372902189641809)
      ·
        refine ⟨3304144876029676642231357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4405526501372902189641809 3304144876029676642231357)
        ·
          refine ⟨1239054328511128740836759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3304144876029676642231357 1239054328511128740836759)
          ·
            refine ⟨1858581492766693111255139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1239054328511128740836759 1858581492766693111255139)
            ·
              refine ⟨2787872239150039666882709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1858581492766693111255139 2787872239150039666882709)
              ·
                refine ⟨130681511210158109385127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2787872239150039666882709 130681511210158109385127)
                ·
                  rfl

theorem cell20_858942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 1, 6].length) (baseStart_858942 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_858942 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_858942 prefixEnd_858942 := by exact prefixLift 858942
  have htrace : WordTrace (prefixWord ++ tailWord_858942) baseStart_858942 baseEnd_858942 := by
    simpa [prefixWord, tailWord_858942, baseEnd_858942] using wordTrace_append hprefix tailTrace_858942
  have hstable : (prefixWord ++ tailWord_858942).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_858942).length < 2 ^ (prefixWord ++ tailWord_858942).sum := by decide
  have hdescent : baseEnd_858942 < baseStart_858942 := by decide
  rcases family_descends (prefixWord ++ tailWord_858942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_858948 : List Nat := [2, 3, 4, 2, 1, 2, 1, 3, 2]
def baseStart_858948 : Nat := 118140960795 + 858948 * 2 ^ 59
def prefixEnd_858948 : Nat := 4983230072969 + 3 ^ 40 * 858948 * 2
def baseEnd_858948 : Nat := 392047272193964973955357

theorem tailTrace_858948 : CollatzResearch.WordTrace tailWord_858948 prefixEnd_858948 392047272193964973955357 := by
  unfold tailWord_858948
  simp only [CollatzResearch.WordTrace]
  refine ⟨15664203646092783742196749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20885604861457044989595665 15664203646092783742196749)
  ·
    refine ⟨5874076367284793903323781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15664203646092783742196749 5874076367284793903323781)
    ·
      refine ⟨1101389318865898856873209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5874076367284793903323781 1101389318865898856873209)
      ·
        refine ⟨826041989149424142654907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1101389318865898856873209 826041989149424142654907)
        ·
          refine ⟨1239062983724136213982361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 826041989149424142654907 1239062983724136213982361)
          ·
            refine ⟨929297237793102160486771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1239062983724136213982361 929297237793102160486771)
            ·
              refine ⟨1393945856689653240730157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 929297237793102160486771 1393945856689653240730157)
              ·
                refine ⟨522729696258619965273809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1393945856689653240730157 522729696258619965273809)
                ·
                  refine ⟨392047272193964973955357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 522729696258619965273809 392047272193964973955357)
                  ·
                    rfl

theorem cell20_858948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 1, 3, 2].length) (baseStart_858948 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_858948 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_858948 prefixEnd_858948 := by exact prefixLift 858948
  have htrace : WordTrace (prefixWord ++ tailWord_858948) baseStart_858948 baseEnd_858948 := by
    simpa [prefixWord, tailWord_858948, baseEnd_858948] using wordTrace_append hprefix tailTrace_858948
  have hstable : (prefixWord ++ tailWord_858948).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_858948).length < 2 ^ (prefixWord ++ tailWord_858948).sum := by decide
  have hdescent : baseEnd_858948 < baseStart_858948 := by decide
  rcases family_descends (prefixWord ++ tailWord_858948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_858970 : List Nat := [3, 1, 1, 2, 1, 4, 2, 1, 5]
def baseStart_858970 : Nat := 118140960795 + 858970 * 2 ^ 59
def prefixEnd_858970 : Nat := 4983230072969 + 3 ^ 40 * 858970 * 2
def baseEnd_858970 : Nat := 392057313593430675221933

theorem tailTrace_858970 : CollatzResearch.WordTrace tailWord_858970 prefixEnd_858970 392057313593430675221933 := by
  unfold tailWord_858970
  simp only [CollatzResearch.WordTrace]
  refine ⟨7832302424526466310423591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20886139798737243494462909 7832302424526466310423591)
  ·
    refine ⟨11748453636789699465635387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7832302424526466310423591 11748453636789699465635387)
    ·
      refine ⟨17622680455184549198453081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11748453636789699465635387 17622680455184549198453081)
      ·
        refine ⟨13217010341388411898839811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17622680455184549198453081 13217010341388411898839811)
        ·
          refine ⟨19825515512082617848259717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13217010341388411898839811 19825515512082617848259717)
          ·
            refine ⟨3717284158515490846548697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19825515512082617848259717 3717284158515490846548697)
            ·
              refine ⟨2787963118886618134911523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3717284158515490846548697 2787963118886618134911523)
              ·
                refine ⟨4181944678329927202367285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2787963118886618134911523 4181944678329927202367285)
                ·
                  refine ⟨392057313593430675221933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4181944678329927202367285 392057313593430675221933)
                  ·
                    rfl

theorem cell20_858970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 2, 1, 5].length) (baseStart_858970 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_858970 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_858970 prefixEnd_858970 := by exact prefixLift 858970
  have htrace : WordTrace (prefixWord ++ tailWord_858970) baseStart_858970 baseEnd_858970 := by
    simpa [prefixWord, tailWord_858970, baseEnd_858970] using wordTrace_append hprefix tailTrace_858970
  have hstable : (prefixWord ++ tailWord_858970).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_858970).length < 2 ^ (prefixWord ++ tailWord_858970).sum := by decide
  have hdescent : baseEnd_858970 < baseStart_858970 := by decide
  rcases family_descends (prefixWord ++ tailWord_858970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_858977 : List Nat := [1, 2, 3, 1, 1, 1, 2, 5, 4]
def baseStart_858977 : Nat := 118140960795 + 858977 * 2 ^ 59
def prefixEnd_858977 : Nat := 4983230072969 + 3 ^ 40 * 858977 * 2
def baseEnd_858977 : Nat := 392060508584169761988571

theorem tailTrace_858977 : CollatzResearch.WordTrace tailWord_858977 prefixEnd_858977 392060508584169761988571 := by
  unfold tailWord_858977
  simp only [CollatzResearch.WordTrace]
  refine ⟨31329465009080505437199185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20886310006053670291466123 31329465009080505437199185)
  ·
    refine ⟨23497098756810379077899389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31329465009080505437199185 23497098756810379077899389)
    ·
      refine ⟨8811412033803892154212271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23497098756810379077899389 8811412033803892154212271)
      ·
        refine ⟨13217118050705838231318407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8811412033803892154212271 13217118050705838231318407)
        ·
          refine ⟨19825677076058757346977611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13217118050705838231318407 19825677076058757346977611)
          ·
            refine ⟨29738515614088136020466417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19825677076058757346977611 29738515614088136020466417)
            ·
              refine ⟨22303886710566102015349813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29738515614088136020466417 22303886710566102015349813)
              ·
                refine ⟨2090989379115572063939045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22303886710566102015349813 2090989379115572063939045)
                ·
                  refine ⟨392060508584169761988571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2090989379115572063939045 392060508584169761988571)
                  ·
                    rfl

theorem cell20_858977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 5, 4].length) (baseStart_858977 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_858977 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_858977 prefixEnd_858977 := by exact prefixLift 858977
  have htrace : WordTrace (prefixWord ++ tailWord_858977) baseStart_858977 baseEnd_858977 := by
    simpa [prefixWord, tailWord_858977, baseEnd_858977] using wordTrace_append hprefix tailTrace_858977
  have hstable : (prefixWord ++ tailWord_858977).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_858977).length < 2 ^ (prefixWord ++ tailWord_858977).sum := by decide
  have hdescent : baseEnd_858977 < baseStart_858977 := by decide
  rcases family_descends (prefixWord ++ tailWord_858977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_858987 : List Nat := [1, 1, 1, 1, 2, 2, 8, 1, 3]
def baseStart_858987 : Nat := 118140960795 + 858987 * 2 ^ 59
def prefixEnd_858987 : Nat := 4983230072969 + 3 ^ 40 * 858987 * 2
def baseEnd_858987 : Nat := 392065072856654171655197

theorem tailTrace_858987 : CollatzResearch.WordTrace tailWord_858987 prefixEnd_858987 392065072856654171655197 := by
  unfold tailWord_858987
  simp only [CollatzResearch.WordTrace]
  refine ⟨31329829739044277145063215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20886553159362851430042143 31329829739044277145063215)
  ·
    refine ⟨46994744608566415717594823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31329829739044277145063215 46994744608566415717594823)
    ·
      refine ⟨70492116912849623576392235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46994744608566415717594823 70492116912849623576392235)
      ·
        refine ⟨105738175369274435364588353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70492116912849623576392235 105738175369274435364588353)
        ·
          refine ⟨79303631526955826523441265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105738175369274435364588353 79303631526955826523441265)
          ·
            refine ⟨59477723645216869892580949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79303631526955826523441265 59477723645216869892580949)
            ·
              refine ⟨697004573967385194053683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 59477723645216869892580949 697004573967385194053683)
              ·
                refine ⟨1045506860951077791080525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 697004573967385194053683 1045506860951077791080525)
                ·
                  refine ⟨392065072856654171655197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1045506860951077791080525 392065072856654171655197)
                  ·
                    rfl

theorem cell20_858987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 8, 1, 3].length) (baseStart_858987 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_858987 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_858987 prefixEnd_858987 := by exact prefixLift 858987
  have htrace : WordTrace (prefixWord ++ tailWord_858987) baseStart_858987 baseEnd_858987 := by
    simpa [prefixWord, tailWord_858987, baseEnd_858987] using wordTrace_append hprefix tailTrace_858987
  have hstable : (prefixWord ++ tailWord_858987).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_858987).length < 2 ^ (prefixWord ++ tailWord_858987).sum := by decide
  have hdescent : baseEnd_858987 < baseStart_858987 := by decide
  rcases family_descends (prefixWord ++ tailWord_858987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_859022 : List Nat := [4, 1, 1, 14]
def baseStart_859022 : Nat := 118140960795 + 859022 * 2 ^ 59
def prefixEnd_859022 : Nat := 4983230072969 + 3 ^ 40 * 859022 * 2
def baseEnd_859022 : Nat := 1613502254363578623409

theorem tailTrace_859022 : CollatzResearch.WordTrace tailWord_859022 prefixEnd_859022 1613502254363578623409 := by
  unfold tailWord_859022
  simp only [CollatzResearch.WordTrace]
  refine ⟨3916388286739684765323415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20887404195944985415058213 3916388286739684765323415)
  ·
    refine ⟨5874582430109527147985123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3916388286739684765323415 5874582430109527147985123)
    ·
      refine ⟨8811873645164290721977685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5874582430109527147985123 8811873645164290721977685)
      ·
        refine ⟨1613502254363578623409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 14 8811873645164290721977685 1613502254363578623409)
        ·
          rfl

theorem cell20_859022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 14].length) (baseStart_859022 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_859022 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_859022 prefixEnd_859022 := by exact prefixLift 859022
  have htrace : WordTrace (prefixWord ++ tailWord_859022) baseStart_859022 baseEnd_859022 := by
    simpa [prefixWord, tailWord_859022, baseEnd_859022] using wordTrace_append hprefix tailTrace_859022
  have hstable : (prefixWord ++ tailWord_859022).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_859022).length < 2 ^ (prefixWord ++ tailWord_859022).sum := by decide
  have hdescent : baseEnd_859022 < baseStart_859022 := by decide
  rcases family_descends (prefixWord ++ tailWord_859022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_859039 : List Nat := [1, 1, 2, 5, 2, 1, 3, 5]
def baseStart_859039 : Nat := 118140960795 + 859039 * 2 ^ 59
def prefixEnd_859039 : Nat := 4983230072969 + 3 ^ 40 * 859039 * 2
def baseEnd_859039 : Nat := 130696269024524367307217

theorem tailTrace_859039 : CollatzResearch.WordTrace tailWord_859039 prefixEnd_859039 130696269024524367307217 := by
  unfold tailWord_859039
  simp only [CollatzResearch.WordTrace]
  refine ⟨31331726334855890025956171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20887817556570593350637447 31331726334855890025956171)
  ·
    refine ⟨46997589502283835038934257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31331726334855890025956171 46997589502283835038934257)
    ·
      refine ⟨35248192126712876279200693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46997589502283835038934257 35248192126712876279200693)
      ·
        refine ⟨3304518011879332151175065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 35248192126712876279200693 3304518011879332151175065)
        ·
          refine ⟨2478388508909499113381299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3304518011879332151175065 2478388508909499113381299)
          ·
            refine ⟨3717582763364248670071949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2478388508909499113381299 3717582763364248670071949)
            ·
              refine ⟨1394093536261593251276981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3717582763364248670071949 1394093536261593251276981)
              ·
                refine ⟨130696269024524367307217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1394093536261593251276981 130696269024524367307217)
                ·
                  rfl

theorem cell20_859039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 3, 5].length) (baseStart_859039 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_859039 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_859039 prefixEnd_859039 := by exact prefixLift 859039
  have htrace : WordTrace (prefixWord ++ tailWord_859039) baseStart_859039 baseEnd_859039 := by
    simpa [prefixWord, tailWord_859039, baseEnd_859039] using wordTrace_append hprefix tailTrace_859039
  have hstable : (prefixWord ++ tailWord_859039).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_859039).length < 2 ^ (prefixWord ++ tailWord_859039).sum := by decide
  have hdescent : baseEnd_859039 < baseStart_859039 := by decide
  rcases family_descends (prefixWord ++ tailWord_859039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_859076 : List Nat := [2, 3, 3, 3, 2, 1, 1, 2, 3]
def baseStart_859076 : Nat := 118140960795 + 859076 * 2 ^ 59
def prefixEnd_859076 : Nat := 4983230072969 + 3 ^ 40 * 859076 * 2
def baseEnd_859076 : Nat := 392105694881765417688167

theorem tailTrace_859076 : CollatzResearch.WordTrace tailWord_859076 prefixEnd_859076 392105694881765417688167 := by
  unfold tailWord_859076
  simp only [CollatzResearch.WordTrace]
  refine ⟨15666537917860922672526541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20888717223814563563368721 15666537917860922672526541)
  ·
    refine ⟨5874951719197846002197453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15666537917860922672526541 5874951719197846002197453)
    ·
      refine ⟨2203106894699192250824045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5874951719197846002197453 2203106894699192250824045)
      ·
        refine ⟨826165085512197094059017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2203106894699192250824045 826165085512197094059017)
        ·
          refine ⟨619623814134147820544263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 826165085512197094059017 619623814134147820544263)
          ·
            refine ⟨929435721201221730816395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 619623814134147820544263 929435721201221730816395)
            ·
              refine ⟨1394153581801832596224593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 929435721201221730816395 1394153581801832596224593)
              ·
                refine ⟨1045615186351374447168445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1394153581801832596224593 1045615186351374447168445)
                ·
                  refine ⟨392105694881765417688167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1045615186351374447168445 392105694881765417688167)
                  ·
                    rfl

theorem cell20_859076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 1, 2, 3].length) (baseStart_859076 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_859076 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_859076 prefixEnd_859076 := by exact prefixLift 859076
  have htrace : WordTrace (prefixWord ++ tailWord_859076) baseStart_859076 baseEnd_859076 := by
    simpa [prefixWord, tailWord_859076, baseEnd_859076] using wordTrace_append hprefix tailTrace_859076
  have hstable : (prefixWord ++ tailWord_859076).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_859076).length < 2 ^ (prefixWord ++ tailWord_859076).sum := by decide
  have hdescent : baseEnd_859076 < baseStart_859076 := by decide
  rcases family_descends (prefixWord ++ tailWord_859076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_859080 : List Nat := [2, 1, 3, 1, 5, 2, 1, 2, 3]
def baseStart_859080 : Nat := 118140960795 + 859080 * 2 ^ 59
def prefixEnd_859080 : Nat := 4983230072969 + 3 ^ 40 * 859080 * 2
def baseEnd_859080 : Nat := 392107520590759181554817

theorem tailTrace_859080 : CollatzResearch.WordTrace tailWord_859080 prefixEnd_859080 392107520590759181554817 := by
  unfold tailWord_859080
  simp only [CollatzResearch.WordTrace]
  refine ⟨15666610863853677014099347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20888814485138236018799129 15666610863853677014099347)
  ·
    refine ⟨23499916295780515521149021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15666610863853677014099347 23499916295780515521149021)
    ·
      refine ⟨8812468610917693320430883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23499916295780515521149021 8812468610917693320430883)
      ·
        refine ⟨13218702916376539980646325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8812468610917693320430883 13218702916376539980646325)
        ·
          refine ⟨1239253398410300623185593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13218702916376539980646325 1239253398410300623185593)
          ·
            refine ⟨929440048807725467389195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1239253398410300623185593 929440048807725467389195)
            ·
              refine ⟨1394160073211588201083793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 929440048807725467389195 1394160073211588201083793)
              ·
                refine ⟨1045620054908691150812845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1394160073211588201083793 1045620054908691150812845)
                ·
                  refine ⟨392107520590759181554817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1045620054908691150812845 392107520590759181554817)
                  ·
                    rfl

theorem cell20_859080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 1, 2, 3].length) (baseStart_859080 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_859080 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_859080 prefixEnd_859080 := by exact prefixLift 859080
  have htrace : WordTrace (prefixWord ++ tailWord_859080) baseStart_859080 baseEnd_859080 := by
    simpa [prefixWord, tailWord_859080, baseEnd_859080] using wordTrace_append hprefix tailTrace_859080
  have hstable : (prefixWord ++ tailWord_859080).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_859080).length < 2 ^ (prefixWord ++ tailWord_859080).sum := by decide
  have hdescent : baseEnd_859080 < baseStart_859080 := by decide
  rcases family_descends (prefixWord ++ tailWord_859080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_859084 : List Nat := [2, 2, 1, 4, 1, 1, 3, 1, 5]
def baseStart_859084 : Nat := 118140960795 + 859084 * 2 ^ 59
def prefixEnd_859084 : Nat := 4983230072969 + 3 ^ 40 * 859084 * 2
def baseEnd_859084 : Nat := 392109346299752945421467

theorem tailTrace_859084 : CollatzResearch.WordTrace tailWord_859084 prefixEnd_859084 392109346299752945421467 := by
  unfold tailWord_859084
  simp only [CollatzResearch.WordTrace]
  refine ⟨15666683809846431355672153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20888911746461908474229537 15666683809846431355672153)
  ·
    refine ⟨11750012857384823516754115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15666683809846431355672153 11750012857384823516754115)
    ·
      refine ⟨17625019286077235275131173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11750012857384823516754115 17625019286077235275131173)
      ·
        refine ⟨3304691116139481614087095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17625019286077235275131173 3304691116139481614087095)
        ·
          refine ⟨4957036674209222421130643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3304691116139481614087095 4957036674209222421130643)
          ·
            refine ⟨7435555011313833631695965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4957036674209222421130643 7435555011313833631695965)
            ·
              refine ⟨2788333129242687611885987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7435555011313833631695965 2788333129242687611885987)
              ·
                refine ⟨4182499693864031417828981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2788333129242687611885987 4182499693864031417828981)
                ·
                  refine ⟨392109346299752945421467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4182499693864031417828981 392109346299752945421467)
                  ·
                    rfl

theorem cell20_859084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 3, 1, 5].length) (baseStart_859084 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_859084 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_859084 prefixEnd_859084 := by exact prefixLift 859084
  have htrace : WordTrace (prefixWord ++ tailWord_859084) baseStart_859084 baseEnd_859084 := by
    simpa [prefixWord, tailWord_859084, baseEnd_859084] using wordTrace_append hprefix tailTrace_859084
  have hstable : (prefixWord ++ tailWord_859084).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_859084).length < 2 ^ (prefixWord ++ tailWord_859084).sum := by decide
  have hdescent : baseEnd_859084 < baseStart_859084 := by decide
  rcases family_descends (prefixWord ++ tailWord_859084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_859138 : List Nat := [3, 4, 1, 3, 1, 1, 3, 2, 2]
def baseStart_859138 : Nat := 118140960795 + 859138 * 2 ^ 59
def prefixEnd_859138 : Nat := 4983230072969 + 3 ^ 40 * 859138 * 2
def baseEnd_859138 : Nat := 392133993371168757621247

theorem tailTrace_859138 : CollatzResearch.WordTrace tailWord_859138 prefixEnd_859138 392133993371168757621247 := by
  unfold tailWord_859138
  simp only [CollatzResearch.WordTrace]
  refine ⟨7833834290374307483452517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20890224774331486622540045 7833834290374307483452517)
  ·
    refine ⟨1468843929445182653147347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7833834290374307483452517 1468843929445182653147347)
    ·
      refine ⟨2203265894167773979721021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1468843929445182653147347 2203265894167773979721021)
      ·
        refine ⟨826224710312915242395383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2203265894167773979721021 826224710312915242395383)
        ·
          refine ⟨1239337065469372863593075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 826224710312915242395383 1239337065469372863593075)
          ·
            refine ⟨1859005598204059295389613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1239337065469372863593075 1859005598204059295389613)
            ·
              refine ⟨697127099326522235771105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1859005598204059295389613 697127099326522235771105)
              ·
                refine ⟨522845324494891676828329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 697127099326522235771105 522845324494891676828329)
                ·
                  refine ⟨392133993371168757621247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 522845324494891676828329 392133993371168757621247)
                  ·
                    rfl

theorem cell20_859138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 3, 2, 2].length) (baseStart_859138 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_859138 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_859138 prefixEnd_859138 := by exact prefixLift 859138
  have htrace : WordTrace (prefixWord ++ tailWord_859138) baseStart_859138 baseEnd_859138 := by
    simpa [prefixWord, tailWord_859138, baseEnd_859138] using wordTrace_append hprefix tailTrace_859138
  have hstable : (prefixWord ++ tailWord_859138).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_859138).length < 2 ^ (prefixWord ++ tailWord_859138).sum := by decide
  have hdescent : baseEnd_859138 < baseStart_859138 := by decide
  rcases family_descends (prefixWord ++ tailWord_859138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_859146 : List Nat := [3, 1, 2, 2, 3, 1, 3, 1, 4]
def baseStart_859146 : Nat := 118140960795 + 859146 * 2 ^ 59
def prefixEnd_859146 : Nat := 4983230072969 + 3 ^ 40 * 859146 * 2
def baseEnd_859146 : Nat := 392137644789156285354547

theorem tailTrace_859146 : CollatzResearch.WordTrace tailWord_859146 prefixEnd_859146 392137644789156285354547 := by
  unfold tailWord_859146
  simp only [CollatzResearch.WordTrace]
  refine ⟨7833907236367061825025323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20890419296978831533400861 7833907236367061825025323)
  ·
    refine ⟨11750860854550592737537985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7833907236367061825025323 11750860854550592737537985)
    ·
      refine ⟨8813145640912944553153489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11750860854550592737537985 8813145640912944553153489)
      ·
        refine ⟨6609859230684708414865117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8813145640912944553153489 6609859230684708414865117)
        ·
          refine ⟨2478697211506765655574419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6609859230684708414865117 2478697211506765655574419)
          ·
            refine ⟨3718045817260148483361629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2478697211506765655574419 3718045817260148483361629)
            ·
              refine ⟨1394267181472555681260611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3718045817260148483361629 1394267181472555681260611)
              ·
                refine ⟨2091400772208833521890917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1394267181472555681260611 2091400772208833521890917)
                ·
                  refine ⟨392137644789156285354547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2091400772208833521890917 392137644789156285354547)
                  ·
                    rfl

theorem cell20_859146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 3, 1, 4].length) (baseStart_859146 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_859146 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_859146 prefixEnd_859146 := by exact prefixLift 859146
  have htrace : WordTrace (prefixWord ++ tailWord_859146) baseStart_859146 baseEnd_859146 := by
    simpa [prefixWord, tailWord_859146, baseEnd_859146] using wordTrace_append hprefix tailTrace_859146
  have hstable : (prefixWord ++ tailWord_859146).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_859146).length < 2 ^ (prefixWord ++ tailWord_859146).sum := by decide
  have hdescent : baseEnd_859146 < baseStart_859146 := by decide
  rcases family_descends (prefixWord ++ tailWord_859146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_859184 : List Nat := [2, 1, 1, 1, 2, 4, 2, 5, 2]
def baseStart_859184 : Nat := 118140960795 + 859184 * 2 ^ 59
def prefixEnd_859184 : Nat := 4983230072969 + 3 ^ 40 * 859184 * 2
def baseEnd_859184 : Nat := 392154989024597042087725

theorem tailTrace_859184 : CollatzResearch.WordTrace tailWord_859184 prefixEnd_859184 392154989024597042087725 := by
  unfold tailWord_859184
  simp only [CollatzResearch.WordTrace]
  refine ⟨15668507459665289894992303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20891343279553719859989737 15668507459665289894992303)
  ·
    refine ⟨23502761189497934842488455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15668507459665289894992303 23502761189497934842488455)
    ·
      refine ⟨35254141784246902263732683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23502761189497934842488455 35254141784246902263732683)
      ·
        refine ⟨52881212676370353395599025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35254141784246902263732683 52881212676370353395599025)
        ·
          refine ⟨39660909507277765046699269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52881212676370353395599025 39660909507277765046699269)
          ·
            refine ⟨7436420532614580946256113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39660909507277765046699269 7436420532614580946256113)
            ·
              refine ⟨5577315399460935709692085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7436420532614580946256113 5577315399460935709692085)
              ·
                refine ⟨522873318699462722783633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5577315399460935709692085 522873318699462722783633)
                ·
                  refine ⟨392154989024597042087725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 522873318699462722783633 392154989024597042087725)
                  ·
                    rfl

theorem cell20_859184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 5, 2].length) (baseStart_859184 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_859184 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_859184 prefixEnd_859184 := by exact prefixLift 859184
  have htrace : WordTrace (prefixWord ++ tailWord_859184) baseStart_859184 baseEnd_859184 := by
    simpa [prefixWord, tailWord_859184, baseEnd_859184] using wordTrace_append hprefix tailTrace_859184
  have hstable : (prefixWord ++ tailWord_859184).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_859184).length < 2 ^ (prefixWord ++ tailWord_859184).sum := by decide
  have hdescent : baseEnd_859184 < baseStart_859184 := by decide
  rcases family_descends (prefixWord ++ tailWord_859184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_859239 : List Nat := [1, 1, 5, 1, 1, 4, 2, 3, 2]
def baseStart_859239 : Nat := 118140960795 + 859239 * 2 ^ 59
def prefixEnd_859239 : Nat := 4983230072969 + 3 ^ 40 * 859239 * 2
def baseEnd_859239 : Nat := 392180092523261295254167

theorem tailTrace_859239 : CollatzResearch.WordTrace tailWord_859239 prefixEnd_859239 392180092523261295254167 := by
  unfold tailWord_859239
  simp only [CollatzResearch.WordTrace]
  refine ⟨31339020934131324183236771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20892680622754216122157847 31339020934131324183236771)
  ·
    refine ⟨47008531401196986274855157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31339020934131324183236771 47008531401196986274855157)
    ·
      refine ⟨4407049818862217463267671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 47008531401196986274855157 4407049818862217463267671)
      ·
        refine ⟨6610574728293326194901507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4407049818862217463267671 6610574728293326194901507)
        ·
          refine ⟨9915862092439989292352261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6610574728293326194901507 9915862092439989292352261)
          ·
            refine ⟨1859224142332497992316049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9915862092439989292352261 1859224142332497992316049)
            ·
              refine ⟨1394418106749373494237037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1859224142332497992316049 1394418106749373494237037)
              ·
                refine ⟨522906790031015060338889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1394418106749373494237037 522906790031015060338889)
                ·
                  refine ⟨392180092523261295254167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 522906790031015060338889 392180092523261295254167)
                  ·
                    rfl

theorem cell20_859239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 2, 3, 2].length) (baseStart_859239 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_859239 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_859239 prefixEnd_859239 := by exact prefixLift 859239
  have htrace : WordTrace (prefixWord ++ tailWord_859239) baseStart_859239 baseEnd_859239 := by
    simpa [prefixWord, tailWord_859239, baseEnd_859239] using wordTrace_append hprefix tailTrace_859239
  have hstable : (prefixWord ++ tailWord_859239).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_859239).length < 2 ^ (prefixWord ++ tailWord_859239).sum := by decide
  have hdescent : baseEnd_859239 < baseStart_859239 := by decide
  rcases family_descends (prefixWord ++ tailWord_859239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_859250 : List Nat := [3, 2, 1, 2, 2, 1, 9]
def baseStart_859250 : Nat := 118140960795 + 859250 * 2 ^ 59
def prefixEnd_859250 : Nat := 4983230072969 + 3 ^ 40 * 859250 * 2
def baseEnd_859250 : Nat := 43576123691443793987495

theorem tailTrace_859250 : CollatzResearch.WordTrace tailWord_859250 prefixEnd_859250 43576123691443793987495 := by
  unfold tailWord_859250
  simp only [CollatzResearch.WordTrace]
  refine ⟨7834855534272868265471801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20892948091394315374591469 7834855534272868265471801)
  ·
    refine ⟨5876141650704651199103851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7834855534272868265471801 5876141650704651199103851)
    ·
      refine ⟨8814212476056976798655777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5876141650704651199103851 8814212476056976798655777)
      ·
        refine ⟨6610659357042732598991833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8814212476056976798655777 6610659357042732598991833)
        ·
          refine ⟨4957994517782049449243875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6610659357042732598991833 4957994517782049449243875)
          ·
            refine ⟨7436991776673074173865813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4957994517782049449243875 7436991776673074173865813)
            ·
              refine ⟨43576123691443793987495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7436991776673074173865813 43576123691443793987495)
              ·
                rfl

theorem cell20_859250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 9].length) (baseStart_859250 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_859250 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_859250 prefixEnd_859250 := by exact prefixLift 859250
  have htrace : WordTrace (prefixWord ++ tailWord_859250) baseStart_859250 baseEnd_859250 := by
    simpa [prefixWord, tailWord_859250, baseEnd_859250] using wordTrace_append hprefix tailTrace_859250
  have hstable : (prefixWord ++ tailWord_859250).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_859250).length < 2 ^ (prefixWord ++ tailWord_859250).sum := by decide
  have hdescent : baseEnd_859250 < baseStart_859250 := by decide
  rcases family_descends (prefixWord ++ tailWord_859250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_859260 : List Nat := [2, 2, 2, 1, 1, 3, 1, 6, 2]
def baseStart_859260 : Nat := 118140960795 + 859260 * 2 ^ 59
def prefixEnd_859260 : Nat := 4983230072969 + 3 ^ 40 * 859260 * 2
def baseEnd_859260 : Nat := 392189677495478555554081

theorem tailTrace_859260 : CollatzResearch.WordTrace tailWord_859260 prefixEnd_859260 392189677495478555554081 := by
  unfold tailWord_859260
  simp only [CollatzResearch.WordTrace]
  refine ⟨15669893433527622384875617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20893191244703496513167489 15669893433527622384875617)
  ·
    refine ⟨11752420075145716788656713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15669893433527622384875617 11752420075145716788656713)
    ·
      refine ⟨8814315056359287591492535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11752420075145716788656713 8814315056359287591492535)
      ·
        refine ⟨13221472584538931387238803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8814315056359287591492535 13221472584538931387238803)
        ·
          refine ⟨19832208876808397080858205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13221472584538931387238803 19832208876808397080858205)
          ·
            refine ⟨7437078328803148905321827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19832208876808397080858205 7437078328803148905321827)
            ·
              refine ⟨11155617493204723357982741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7437078328803148905321827 11155617493204723357982741)
              ·
                refine ⟨522919569993971407405441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 11155617493204723357982741 522919569993971407405441)
                ·
                  refine ⟨392189677495478555554081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 522919569993971407405441 392189677495478555554081)
                  ·
                    rfl

theorem cell20_859260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 6, 2].length) (baseStart_859260 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_859260 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_859260 prefixEnd_859260 := by exact prefixLift 859260
  have htrace : WordTrace (prefixWord ++ tailWord_859260) baseStart_859260 baseEnd_859260 := by
    simpa [prefixWord, tailWord_859260, baseEnd_859260] using wordTrace_append hprefix tailTrace_859260
  have hstable : (prefixWord ++ tailWord_859260).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_859260).length < 2 ^ (prefixWord ++ tailWord_859260).sum := by decide
  have hdescent : baseEnd_859260 < baseStart_859260 := by decide
  rcases family_descends (prefixWord ++ tailWord_859260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_859294 : List Nat := [4, 3, 1, 1, 2, 1, 3, 3, 2]
def baseStart_859294 : Nat := 118140960795 + 859294 * 2 ^ 59
def prefixEnd_859294 : Nat := 4983230072969 + 3 ^ 40 * 859294 * 2
def baseEnd_859294 : Nat := 392205196021925548420609

theorem tailTrace_859294 : CollatzResearch.WordTrace tailWord_859294 prefixEnd_859294 392205196021925548420609 := by
  unfold tailWord_859294
  simp only [CollatzResearch.WordTrace]
  refine ⟨3917628368616508572061117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20894017965954712384325957 3917628368616508572061117)
  ·
    refine ⟨1469110638231190714522919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3917628368616508572061117 1469110638231190714522919)
    ·
      refine ⟨2203665957346786071784379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1469110638231190714522919 2203665957346786071784379)
      ·
        refine ⟨3305498936020179107676569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2203665957346786071784379 3305498936020179107676569)
        ·
          refine ⟨2479124202015134330757427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3305498936020179107676569 2479124202015134330757427)
          ·
            refine ⟨3718686303022701496136141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2479124202015134330757427 3718686303022701496136141)
            ·
              refine ⟨1394507363633513061051053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3718686303022701496136141 1394507363633513061051053)
              ·
                refine ⟨522940261362567397894145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1394507363633513061051053 522940261362567397894145)
                ·
                  refine ⟨392205196021925548420609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 522940261362567397894145 392205196021925548420609)
                  ·
                    rfl

theorem cell20_859294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 3, 3, 2].length) (baseStart_859294 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_859294 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_859294 prefixEnd_859294 := by exact prefixLift 859294
  have htrace : WordTrace (prefixWord ++ tailWord_859294) baseStart_859294 baseEnd_859294 := by
    simpa [prefixWord, tailWord_859294, baseEnd_859294] using wordTrace_append hprefix tailTrace_859294
  have hstable : (prefixWord ++ tailWord_859294).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_859294).length < 2 ^ (prefixWord ++ tailWord_859294).sum := by decide
  have hdescent : baseEnd_859294 < baseStart_859294 := by decide
  rcases family_descends (prefixWord ++ tailWord_859294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_859370 : List Nat := [3, 1, 3, 1, 1, 5, 2, 2, 2]
def baseStart_859370 : Nat := 118140960795 + 859370 * 2 ^ 59
def prefixEnd_859370 : Nat := 4983230072969 + 3 ^ 40 * 859370 * 2
def baseEnd_859370 : Nat := 392239884492807061886965

theorem tailTrace_859370 : CollatzResearch.WordTrace tailWord_859370 prefixEnd_859370 392239884492807061886965 := by
  unfold tailWord_859370
  simp only [CollatzResearch.WordTrace]
  refine ⟨7835949724164183389063891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20895865931104489037503709 7835949724164183389063891)
  ·
    refine ⟨11753924586246275083595837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7835949724164183389063891 11753924586246275083595837)
    ·
      refine ⟨4407721719842353156348439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11753924586246275083595837 4407721719842353156348439)
      ·
        refine ⟨6611582579763529734522659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4407721719842353156348439 6611582579763529734522659)
        ·
          refine ⟨9917373869645294601783989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6611582579763529734522659 9917373869645294601783989)
          ·
            refine ⟨929753800279246368917249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9917373869645294601783989 929753800279246368917249)
            ·
              refine ⟨697315350209434776687937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 929753800279246368917249 697315350209434776687937)
              ·
                refine ⟨522986512657076082515953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 697315350209434776687937 522986512657076082515953)
                ·
                  refine ⟨392239884492807061886965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 522986512657076082515953 392239884492807061886965)
                  ·
                    rfl

theorem cell20_859370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 2, 2, 2].length) (baseStart_859370 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_859370 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_859370 prefixEnd_859370 := by exact prefixLift 859370
  have htrace : WordTrace (prefixWord ++ tailWord_859370) baseStart_859370 baseEnd_859370 := by
    simpa [prefixWord, tailWord_859370, baseEnd_859370] using wordTrace_append hprefix tailTrace_859370
  have hstable : (prefixWord ++ tailWord_859370).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_859370).length < 2 ^ (prefixWord ++ tailWord_859370).sum := by decide
  have hdescent : baseEnd_859370 < baseStart_859370 := by decide
  rcases family_descends (prefixWord ++ tailWord_859370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_859395 : List Nat := [1, 1, 1, 3, 2, 5, 1, 2, 4]
def baseStart_859395 : Nat := 118140960795 + 859395 * 2 ^ 59
def prefixEnd_859395 : Nat := 4983230072969 + 3 ^ 40 * 859395 * 2
def baseEnd_859395 : Nat := 392251295174018086053529

theorem tailTrace_859395 : CollatzResearch.WordTrace tailWord_859395 prefixEnd_859395 392251295174018086053529 := by
  unfold tailWord_859395
  simp only [CollatzResearch.WordTrace]
  refine ⟨31344710721566162825915639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20896473814377441883943759 31344710721566162825915639)
  ·
    refine ⟨47017066082349244238873459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31344710721566162825915639 47017066082349244238873459)
    ·
      refine ⟨70525599123523866358310189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47017066082349244238873459 70525599123523866358310189)
      ·
        refine ⟨26447099671321449884366321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70525599123523866358310189 26447099671321449884366321)
        ·
          refine ⟨19835324753491087413274741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26447099671321449884366321 19835324753491087413274741)
          ·
            refine ⟨1859561695639789444994507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19835324753491087413274741 1859561695639789444994507)
            ·
              refine ⟨2789342543459684167491761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1859561695639789444994507 2789342543459684167491761)
              ·
                refine ⟨2092006907594763125618821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2789342543459684167491761 2092006907594763125618821)
                ·
                  refine ⟨392251295174018086053529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2092006907594763125618821 392251295174018086053529)
                  ·
                    rfl

theorem cell20_859395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 1, 2, 4].length) (baseStart_859395 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_859395 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_859395 prefixEnd_859395 := by exact prefixLift 859395
  have htrace : WordTrace (prefixWord ++ tailWord_859395) baseStart_859395 baseEnd_859395 := by
    simpa [prefixWord, tailWord_859395, baseEnd_859395] using wordTrace_append hprefix tailTrace_859395
  have hstable : (prefixWord ++ tailWord_859395).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_859395).length < 2 ^ (prefixWord ++ tailWord_859395).sum := by decide
  have hdescent : baseEnd_859395 < baseStart_859395 := by decide
  rcases family_descends (prefixWord ++ tailWord_859395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_859409 : List Nat := [1, 2, 2, 1, 1, 4, 2, 2, 5]
def baseStart_859409 : Nat := 118140960795 + 859409 * 2 ^ 59
def prefixEnd_859409 : Nat := 4983230072969 + 3 ^ 40 * 859409 * 2
def baseEnd_859409 : Nat := 392257685155496259586805

theorem tailTrace_859409 : CollatzResearch.WordTrace tailWord_859409 prefixEnd_859409 392257685155496259586805 := by
  unfold tailWord_859409
  simp only [CollatzResearch.WordTrace]
  refine ⟨31345221343515443216925281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20896814229010295477950187 31345221343515443216925281)
  ·
    refine ⟨23508916007636582412693961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31345221343515443216925281 23508916007636582412693961)
    ·
      refine ⟨17631687005727436809520471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23508916007636582412693961 17631687005727436809520471)
      ·
        refine ⟨26447530508591155214280707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17631687005727436809520471 26447530508591155214280707)
        ·
          refine ⟨39671295762886732821421061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26447530508591155214280707 39671295762886732821421061)
          ·
            refine ⟨7438367955541262404016449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39671295762886732821421061 7438367955541262404016449)
            ·
              refine ⟨5578775966655946803012337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7438367955541262404016449 5578775966655946803012337)
              ·
                refine ⟨4184081974991960102259253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5578775966655946803012337 4184081974991960102259253)
                ·
                  refine ⟨392257685155496259586805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4184081974991960102259253 392257685155496259586805)
                  ·
                    rfl

theorem cell20_859409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 2, 5].length) (baseStart_859409 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_859409 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_859409 prefixEnd_859409 := by exact prefixLift 859409
  have htrace : WordTrace (prefixWord ++ tailWord_859409) baseStart_859409 baseEnd_859409 := by
    simpa [prefixWord, tailWord_859409, baseEnd_859409] using wordTrace_append hprefix tailTrace_859409
  have hstable : (prefixWord ++ tailWord_859409).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_859409).length < 2 ^ (prefixWord ++ tailWord_859409).sum := by decide
  have hdescent : baseEnd_859409 < baseStart_859409 := by decide
  rcases family_descends (prefixWord ++ tailWord_859409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_859422 : List Nat := [4, 3, 2, 1, 2, 1, 1, 1, 5]
def baseStart_859422 : Nat := 118140960795 + 859422 * 2 ^ 59
def prefixEnd_859422 : Nat := 4983230072969 + 3 ^ 40 * 859422 * 2
def baseEnd_859422 : Nat := 392263618709725992153419

theorem tailTrace_859422 : CollatzResearch.WordTrace tailWord_859422 prefixEnd_859422 392263618709725992153419 := by
  unfold tailWord_859422
  simp only [CollatzResearch.WordTrace]
  refine ⟨3918211936558543304643565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20897130328312230958099013 3918211936558543304643565)
  ·
    refine ⟨1469329476209453739241337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3918211936558543304643565 1469329476209453739241337)
    ·
      refine ⟨1101997107157090304431003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1469329476209453739241337 1101997107157090304431003)
      ·
        refine ⟨1652995660735635456646505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1101997107157090304431003 1652995660735635456646505)
        ·
          refine ⟨1239746745551726592484879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1652995660735635456646505 1239746745551726592484879)
          ·
            refine ⟨1859620118327589888727319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1239746745551726592484879 1859620118327589888727319)
            ·
              refine ⟨2789430177491384833090979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1859620118327589888727319 2789430177491384833090979)
              ·
                refine ⟨4184145266237077249636469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2789430177491384833090979 4184145266237077249636469)
                ·
                  refine ⟨392263618709725992153419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4184145266237077249636469 392263618709725992153419)
                  ·
                    rfl

theorem cell20_859422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 1, 1, 5].length) (baseStart_859422 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_859422 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_859422 prefixEnd_859422 := by exact prefixLift 859422
  have htrace : WordTrace (prefixWord ++ tailWord_859422) baseStart_859422 baseEnd_859422 := by
    simpa [prefixWord, tailWord_859422, baseEnd_859422] using wordTrace_append hprefix tailTrace_859422
  have hstable : (prefixWord ++ tailWord_859422).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_859422).length < 2 ^ (prefixWord ++ tailWord_859422).sum := by decide
  have hdescent : baseEnd_859422 < baseStart_859422 := by decide
  rcases family_descends (prefixWord ++ tailWord_859422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_859443 : List Nat := [1, 1, 1, 2, 5, 3, 3, 1, 3]
def baseStart_859443 : Nat := 118140960795 + 859443 * 2 ^ 59
def prefixEnd_859443 : Nat := 4983230072969 + 3 ^ 40 * 859443 * 2
def baseEnd_859443 : Nat := 392273203681943252453333

theorem tailTrace_859443 : CollatzResearch.WordTrace tailWord_859443 prefixEnd_859443 392273203681943252453333 := by
  unfold tailWord_859443
  simp only [CollatzResearch.WordTrace]
  refine ⟨31346461425392267023662983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20897640950261511349108655 31346461425392267023662983)
  ·
    refine ⟨47019692138088400535494475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31346461425392267023662983 47019692138088400535494475)
    ·
      refine ⟨70529538207132600803241713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47019692138088400535494475 70529538207132600803241713)
      ·
        refine ⟨52897153655349450602431285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70529538207132600803241713 52897153655349450602431285)
        ·
          refine ⟨4959108155189010993977933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 52897153655349450602431285 4959108155189010993977933)
          ·
            refine ⟨1859665558195879122741725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4959108155189010993977933 1859665558195879122741725)
            ·
              refine ⟨697374584323454671028147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1859665558195879122741725 697374584323454671028147)
              ·
                refine ⟨1046061876485182006542221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 697374584323454671028147 1046061876485182006542221)
                ·
                  refine ⟨392273203681943252453333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1046061876485182006542221 392273203681943252453333)
                  ·
                    rfl

theorem cell20_859443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 3, 1, 3].length) (baseStart_859443 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_859443 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_859443 prefixEnd_859443 := by exact prefixLift 859443
  have htrace : WordTrace (prefixWord ++ tailWord_859443) baseStart_859443 baseEnd_859443 := by
    simpa [prefixWord, tailWord_859443, baseEnd_859443] using wordTrace_append hprefix tailTrace_859443
  have hstable : (prefixWord ++ tailWord_859443).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_859443).length < 2 ^ (prefixWord ++ tailWord_859443).sum := by decide
  have hdescent : baseEnd_859443 < baseStart_859443 := by decide
  rcases family_descends (prefixWord ++ tailWord_859443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_859453 : List Nat := [1, 4, 1, 5, 1, 2, 2, 4]
def baseStart_859453 : Nat := 118140960795 + 859453 * 2 ^ 59
def prefixEnd_859453 : Nat := 4983230072969 + 3 ^ 40 * 859453 * 2
def baseEnd_859453 : Nat := 130759255984809220706653

theorem tailTrace_859453 : CollatzResearch.WordTrace tailWord_859453 prefixEnd_859453 130759255984809220706653 := by
  unfold tailWord_859453
  simp only [CollatzResearch.WordTrace]
  refine ⟨31346826155356038731527013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20897884103570692487684675 31346826155356038731527013)
  ·
    refine ⟨5877529904129257262161315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31346826155356038731527013 5877529904129257262161315)
    ·
      refine ⟨8816294856193885893241973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5877529904129257262161315 8816294856193885893241973)
      ·
        refine ⟨826527642768176802491435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8816294856193885893241973 826527642768176802491435)
        ·
          refine ⟨1239791464152265203737153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 826527642768176802491435 1239791464152265203737153)
          ·
            refine ⟨929843598114198902802865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1239791464152265203737153 929843598114198902802865)
            ·
              refine ⟨697382698585649177102149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 929843598114198902802865 697382698585649177102149)
              ·
                refine ⟨130759255984809220706653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 697382698585649177102149 130759255984809220706653)
                ·
                  rfl

theorem cell20_859453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 2, 4].length) (baseStart_859453 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_859453 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_859453 prefixEnd_859453 := by exact prefixLift 859453
  have htrace : WordTrace (prefixWord ++ tailWord_859453) baseStart_859453 baseEnd_859453 := by
    simpa [prefixWord, tailWord_859453, baseEnd_859453] using wordTrace_append hprefix tailTrace_859453
  have hstable : (prefixWord ++ tailWord_859453).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_859453).length < 2 ^ (prefixWord ++ tailWord_859453).sum := by decide
  have hdescent : baseEnd_859453 < baseStart_859453 := by decide
  rcases family_descends (prefixWord ++ tailWord_859453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_859457 : List Nat := [1, 2, 5, 2, 1, 2, 1, 6]
def baseStart_859457 : Nat := 118140960795 + 859457 * 2 ^ 59
def prefixEnd_859457 : Nat := 4983230072969 + 3 ^ 40 * 859457 * 2
def baseEnd_859457 : Nat := 130759864554473808662203

theorem tailTrace_859457 : CollatzResearch.WordTrace tailWord_859457 prefixEnd_859457 130759864554473808662203 := by
  unfold tailWord_859457
  simp only [CollatzResearch.WordTrace]
  refine ⟨31346972047341547414672625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20897981364894364943115083 31346972047341547414672625)
  ·
    refine ⟨23510229035506160561004469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31346972047341547414672625 23510229035506160561004469)
    ·
      refine ⟨2204083972078702552594169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 23510229035506160561004469 2204083972078702552594169)
      ·
        refine ⟨1653062979059026914445627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2204083972078702552594169 1653062979059026914445627)
        ·
          refine ⟨2479594468588540371668441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1653062979059026914445627 2479594468588540371668441)
          ·
            refine ⟨1859695851441405278751331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2479594468588540371668441 1859695851441405278751331)
            ·
              refine ⟨2789543777162107918126997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1859695851441405278751331 2789543777162107918126997)
              ·
                refine ⟨130759864554473808662203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2789543777162107918126997 130759864554473808662203)
                ·
                  rfl

theorem cell20_859457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 1, 6].length) (baseStart_859457 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_859457 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_859457 prefixEnd_859457 := by exact prefixLift 859457
  have htrace : WordTrace (prefixWord ++ tailWord_859457) baseStart_859457 baseEnd_859457 := by
    simpa [prefixWord, tailWord_859457, baseEnd_859457] using wordTrace_append hprefix tailTrace_859457
  have hstable : (prefixWord ++ tailWord_859457).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_859457).length < 2 ^ (prefixWord ++ tailWord_859457).sum := by decide
  have hdescent : baseEnd_859457 < baseStart_859457 := by decide
  rcases family_descends (prefixWord ++ tailWord_859457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_859488 : List Nat := [2, 1, 1, 3, 4, 3, 1, 1, 4]
def baseStart_859488 : Nat := 118140960795 + 859488 * 2 ^ 59
def prefixEnd_859488 : Nat := 4983230072969 + 3 ^ 40 * 859488 * 2
def baseEnd_859488 : Nat := 392293742908123095953149

theorem tailTrace_859488 : CollatzResearch.WordTrace tailWord_859488 prefixEnd_859488 392293742908123095953149 := by
  unfold tailWord_859488
  simp only [CollatzResearch.WordTrace]
  refine ⟨15674051355114619854525559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20898735140152826472700745 15674051355114619854525559)
  ·
    refine ⟨23511077032671929781788339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15674051355114619854525559 23511077032671929781788339)
    ·
      refine ⟨35266615549007894672682509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23511077032671929781788339 35266615549007894672682509)
      ·
        refine ⟨13224980830877960502255941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35266615549007894672682509 13224980830877960502255941)
        ·
          refine ⟨2479683905789617594172989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13224980830877960502255941 2479683905789617594172989)
          ·
            refine ⟨929881464671106597814871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2479683905789617594172989 929881464671106597814871)
            ·
              refine ⟨1394822197006659896722307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 929881464671106597814871 1394822197006659896722307)
              ·
                refine ⟨2092233295509989845083461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1394822197006659896722307 2092233295509989845083461)
                ·
                  refine ⟨392293742908123095953149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2092233295509989845083461 392293742908123095953149)
                  ·
                    rfl

theorem cell20_859488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 1, 1, 4].length) (baseStart_859488 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_859488 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_859488 prefixEnd_859488 := by exact prefixLift 859488
  have htrace : WordTrace (prefixWord ++ tailWord_859488) baseStart_859488 baseEnd_859488 := by
    simpa [prefixWord, tailWord_859488, baseEnd_859488] using wordTrace_append hprefix tailTrace_859488
  have hstable : (prefixWord ++ tailWord_859488).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_859488).length < 2 ^ (prefixWord ++ tailWord_859488).sum := by decide
  have hdescent : baseEnd_859488 < baseStart_859488 := by decide
  rcases family_descends (prefixWord ++ tailWord_859488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_859495 : List Nat := [1, 1, 5, 1, 4, 1, 2, 5]
def baseStart_859495 : Nat := 118140960795 + 859495 * 2 ^ 59
def prefixEnd_859495 : Nat := 4983230072969 + 3 ^ 40 * 859495 * 2
def baseEnd_859495 : Nat := 130765645966287394239929

theorem tailTrace_859495 : CollatzResearch.WordTrace tailWord_859495 prefixEnd_859495 130765645966287394239929 := by
  unfold tailWord_859495
  simp only [CollatzResearch.WordTrace]
  refine ⟨31348358021203879904555939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20898905347469253269703959 31348358021203879904555939)
  ·
    refine ⟨47022537031805819856833909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31348358021203879904555939 47022537031805819856833909)
    ·
      refine ⟨4408362846731795611578179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 47022537031805819856833909 4408362846731795611578179)
      ·
        refine ⟨6612544270097693417367269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4408362846731795611578179 6612544270097693417367269)
        ·
          refine ⟨1239852050643317515756363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6612544270097693417367269 1239852050643317515756363)
          ·
            refine ⟨1859778075964976273634545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1239852050643317515756363 1859778075964976273634545)
            ·
              refine ⟨1394833556973732205225909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1859778075964976273634545 1394833556973732205225909)
              ·
                refine ⟨130765645966287394239929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1394833556973732205225909 130765645966287394239929)
                ·
                  rfl

theorem cell20_859495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 2, 5].length) (baseStart_859495 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_859495 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_859495 prefixEnd_859495 := by exact prefixLift 859495
  have htrace : WordTrace (prefixWord ++ tailWord_859495) baseStart_859495 baseEnd_859495 := by
    simpa [prefixWord, tailWord_859495, baseEnd_859495] using wordTrace_append hprefix tailTrace_859495
  have hstable : (prefixWord ++ tailWord_859495).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_859495).length < 2 ^ (prefixWord ++ tailWord_859495).sum := by decide
  have hdescent : baseEnd_859495 < baseStart_859495 := by decide
  rcases family_descends (prefixWord ++ tailWord_859495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_859623 : List Nat := [1, 1, 5, 2, 1, 2, 2, 2, 4]
def baseStart_859623 : Nat := 118140960795 + 859623 * 2 ^ 59
def prefixEnd_859623 : Nat := 4983230072969 + 3 ^ 40 * 859623 * 2
def baseEnd_859623 : Nat := 392355360586662626452597

theorem tailTrace_859623 : CollatzResearch.WordTrace tailWord_859623 prefixEnd_859623 392355360586662626452597 := by
  unfold tailWord_859623
  simp only [CollatzResearch.WordTrace]
  refine ⟨31353026564740157765215523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20902017709826771843477015 31353026564740157765215523)
  ·
    refine ⟨47029539847110236647823285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31353026564740157765215523 47029539847110236647823285)
    ·
      refine ⟨4409019360666584685733433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 47029539847110236647823285 4409019360666584685733433)
      ·
        refine ⟨3306764520499938514300075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4409019360666584685733433 3306764520499938514300075)
        ·
          refine ⟨4960146780749907771450113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3306764520499938514300075 4960146780749907771450113)
          ·
            refine ⟨3720110085562430828587585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4960146780749907771450113 3720110085562430828587585)
            ·
              refine ⟨2790082564171823121440689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3720110085562430828587585 2790082564171823121440689)
              ·
                refine ⟨2092561923128867341080517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2790082564171823121440689 2092561923128867341080517)
                ·
                  refine ⟨392355360586662626452597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2092561923128867341080517 392355360586662626452597)
                  ·
                    rfl

theorem cell20_859623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 2, 2, 4].length) (baseStart_859623 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_859623 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_859623 prefixEnd_859623 := by exact prefixLift 859623
  have htrace : WordTrace (prefixWord ++ tailWord_859623) baseStart_859623 baseEnd_859623 := by
    simpa [prefixWord, tailWord_859623, baseEnd_859623] using wordTrace_append hprefix tailTrace_859623
  have hstable : (prefixWord ++ tailWord_859623).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_859623).length < 2 ^ (prefixWord ++ tailWord_859623).sum := by decide
  have hdescent : baseEnd_859623 < baseStart_859623 := by decide
  rcases family_descends (prefixWord ++ tailWord_859623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_859626 : List Nat := [3, 1, 3, 1, 4, 2, 2, 4]
def baseStart_859626 : Nat := 118140960795 + 859626 * 2 ^ 59
def prefixEnd_859626 : Nat := 4983230072969 + 3 ^ 40 * 859626 * 2
def baseEnd_859626 : Nat := 130785576622802649784195

theorem tailTrace_859626 : CollatzResearch.WordTrace tailWord_859626 prefixEnd_859626 130785576622802649784195 := by
  unfold tailWord_859626
  simp only [CollatzResearch.WordTrace]
  refine ⟨7838283995932322319393683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20902090655819526185049821 7838283995932322319393683)
  ·
    refine ⟨11757425993898483479090525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7838283995932322319393683 11757425993898483479090525)
    ·
      refine ⟨4409034747711931304658947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11757425993898483479090525 4409034747711931304658947)
      ·
        refine ⟨6613552121567896956988421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4409034747711931304658947 6613552121567896956988421)
        ·
          refine ⟨1240041022793980679435329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6613552121567896956988421 1240041022793980679435329)
          ·
            refine ⟨930030767095485509576497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1240041022793980679435329 930030767095485509576497)
            ·
              refine ⟨697523075321614132182373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 930030767095485509576497 697523075321614132182373)
              ·
                refine ⟨130785576622802649784195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 697523075321614132182373 130785576622802649784195)
                ·
                  rfl

theorem cell20_859626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 2, 4].length) (baseStart_859626 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_859626 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_859626 prefixEnd_859626 := by exact prefixLift 859626
  have htrace : WordTrace (prefixWord ++ tailWord_859626) baseStart_859626 baseEnd_859626 := by
    simpa [prefixWord, tailWord_859626, baseEnd_859626] using wordTrace_append hprefix tailTrace_859626
  have hstable : (prefixWord ++ tailWord_859626).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_859626).length < 2 ^ (prefixWord ++ tailWord_859626).sum := by decide
  have hdescent : baseEnd_859626 < baseStart_859626 := by decide
  rcases family_descends (prefixWord ++ tailWord_859626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_859630 : List Nat := [4, 1, 2, 1, 2, 1, 3, 6]
def baseStart_859630 : Nat := 118140960795 + 859630 * 2 ^ 59
def prefixEnd_859630 : Nat := 4983230072969 + 3 ^ 40 * 859630 * 2
def baseEnd_859630 : Nat := 130786185192467237739745

theorem tailTrace_859630 : CollatzResearch.WordTrace tailWord_859630 prefixEnd_859630 130786185192467237739745 := by
  unfold tailWord_859630
  simp only [CollatzResearch.WordTrace]
  refine ⟨3919160234464349745090043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20902187917143198640480229 3919160234464349745090043)
  ·
    refine ⟨5878740351696524617635065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3919160234464349745090043 5878740351696524617635065)
    ·
      refine ⟨4409055263772393463226299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5878740351696524617635065 4409055263772393463226299)
      ·
        refine ⟨6613582895658590194839449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4409055263772393463226299 6613582895658590194839449)
        ·
          refine ⟨4960187171743942646129587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6613582895658590194839449 4960187171743942646129587)
          ·
            refine ⟨7440280757615913969194381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4960187171743942646129587 7440280757615913969194381)
            ·
              refine ⟨2790105284105967738447893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7440280757615913969194381 2790105284105967738447893)
              ·
                refine ⟨130786185192467237739745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2790105284105967738447893 130786185192467237739745)
                ·
                  rfl

theorem cell20_859630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 3, 6].length) (baseStart_859630 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_859630 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_859630 prefixEnd_859630 := by exact prefixLift 859630
  have htrace : WordTrace (prefixWord ++ tailWord_859630) baseStart_859630 baseEnd_859630 := by
    simpa [prefixWord, tailWord_859630, baseEnd_859630] using wordTrace_append hprefix tailTrace_859630
  have hstable : (prefixWord ++ tailWord_859630).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_859630).length < 2 ^ (prefixWord ++ tailWord_859630).sum := by decide
  have hdescent : baseEnd_859630 < baseStart_859630 := by decide
  rcases family_descends (prefixWord ++ tailWord_859630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_859640 : List Nat := [2, 1, 2, 1, 1, 5, 3, 3, 2]
def baseStart_859640 : Nat := 118140960795 + 859640 * 2 ^ 59
def prefixEnd_859640 : Nat := 4983230072969 + 3 ^ 40 * 859640 * 2
def baseEnd_859640 : Nat := 392363119849886122885861

theorem tailTrace_859640 : CollatzResearch.WordTrace tailWord_859640 prefixEnd_859640 392363119849886122885861 := by
  unfold tailWord_859640
  simp only [CollatzResearch.WordTrace]
  refine ⟨15676823302839284834292187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20902431070452379779056249 15676823302839284834292187)
  ·
    refine ⟨23515234954258927251438281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15676823302839284834292187 23515234954258927251438281)
    ·
      refine ⟨17636426215694195438578711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23515234954258927251438281 17636426215694195438578711)
      ·
        refine ⟨26454639323541293157868067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17636426215694195438578711 26454639323541293157868067)
        ·
          refine ⟨39681958985311939736802101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26454639323541293157868067 39681958985311939736802101)
          ·
            refine ⟨3720183654872994350325197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 39681958985311939736802101 3720183654872994350325197)
            ·
              refine ⟨1395068870577372881371949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3720183654872994350325197 1395068870577372881371949)
              ·
                refine ⟨523150826466514830514481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1395068870577372881371949 523150826466514830514481)
                ·
                  refine ⟨392363119849886122885861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 523150826466514830514481 392363119849886122885861)
                  ·
                    rfl

theorem cell20_859640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 3, 3, 2].length) (baseStart_859640 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_859640 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_859640 prefixEnd_859640 := by exact prefixLift 859640
  have htrace : WordTrace (prefixWord ++ tailWord_859640) baseStart_859640 baseEnd_859640 := by
    simpa [prefixWord, tailWord_859640, baseEnd_859640] using wordTrace_append hprefix tailTrace_859640
  have hstable : (prefixWord ++ tailWord_859640).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_859640).length < 2 ^ (prefixWord ++ tailWord_859640).sum := by decide
  have hdescent : baseEnd_859640 < baseStart_859640 := by decide
  rcases family_descends (prefixWord ++ tailWord_859640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_859644 : List Nat := [2, 2, 2, 1, 2, 1, 2, 2, 6]
def baseStart_859644 : Nat := 118140960795 + 859644 * 2 ^ 59
def prefixEnd_859644 : Nat := 4983230072969 + 3 ^ 40 * 859644 * 2
def baseEnd_859644 : Nat := 392364945558879886752511

theorem tailTrace_859644 : CollatzResearch.WordTrace tailWord_859644 prefixEnd_859644 392364945558879886752511 := by
  unfold tailWord_859644
  simp only [CollatzResearch.WordTrace]
  refine ⟨15676896248832039175864993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20902528331776052234486657 15676896248832039175864993)
  ·
    refine ⟨11757672186624029381898745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15676896248832039175864993 11757672186624029381898745)
    ·
      refine ⟨8818254139968022036424059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11757672186624029381898745 8818254139968022036424059)
      ·
        refine ⟨13227381209952033054636089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8818254139968022036424059 13227381209952033054636089)
        ·
          refine ⟨9920535907464024790977067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13227381209952033054636089 9920535907464024790977067)
          ·
            refine ⟨14880803861196037186465601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9920535907464024790977067 14880803861196037186465601)
            ·
              refine ⟨11160602895897027889849201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14880803861196037186465601 11160602895897027889849201)
              ·
                refine ⟨8370452171922770917386901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11160602895897027889849201 8370452171922770917386901)
                ·
                  refine ⟨392364945558879886752511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8370452171922770917386901 392364945558879886752511)
                  ·
                    rfl

theorem cell20_859644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 2, 6].length) (baseStart_859644 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_859644 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_859644 prefixEnd_859644 := by exact prefixLift 859644
  have htrace : WordTrace (prefixWord ++ tailWord_859644) baseStart_859644 baseEnd_859644 := by
    simpa [prefixWord, tailWord_859644, baseEnd_859644] using wordTrace_append hprefix tailTrace_859644
  have hstable : (prefixWord ++ tailWord_859644).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_859644).length < 2 ^ (prefixWord ++ tailWord_859644).sum := by decide
  have hdescent : baseEnd_859644 < baseStart_859644 := by decide
  rcases family_descends (prefixWord ++ tailWord_859644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_859709 : List Nat := [1, 4, 1, 3, 3, 1, 2, 2, 3]
def baseStart_859709 : Nat := 118140960795 + 859709 * 2 ^ 59
def prefixEnd_859709 : Nat := 4983230072969 + 3 ^ 40 * 859709 * 2
def baseEnd_859709 : Nat := 392394613330028549585579

theorem tailTrace_859709 : CollatzResearch.WordTrace tailWord_859709 prefixEnd_859709 392394613330028549585579 := by
  unfold tailWord_859709
  simp only [CollatzResearch.WordTrace]
  refine ⟨31356163242428594452846181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20904108828285729635230787 31356163242428594452846181)
  ·
    refine ⟨5879280607955361459908659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31356163242428594452846181 5879280607955361459908659)
    ·
      refine ⟨8818920911933042189862989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5879280607955361459908659 8818920911933042189862989)
      ·
        refine ⟨3307095341974890821198621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8818920911933042189862989 3307095341974890821198621)
        ·
          refine ⟨1240160753240584057949483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3307095341974890821198621 1240160753240584057949483)
          ·
            refine ⟨1860241129860876086924225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1240160753240584057949483 1860241129860876086924225)
            ·
              refine ⟨1395180847395657065193169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1860241129860876086924225 1395180847395657065193169)
              ·
                refine ⟨1046385635546742798894877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1395180847395657065193169 1046385635546742798894877)
                ·
                  refine ⟨392394613330028549585579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1046385635546742798894877 392394613330028549585579)
                  ·
                    rfl

theorem cell20_859709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 2, 2, 3].length) (baseStart_859709 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_859709 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_859709 prefixEnd_859709 := by exact prefixLift 859709
  have htrace : WordTrace (prefixWord ++ tailWord_859709) baseStart_859709 baseEnd_859709 := by
    simpa [prefixWord, tailWord_859709, baseEnd_859709] using wordTrace_append hprefix tailTrace_859709
  have hstable : (prefixWord ++ tailWord_859709).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_859709).length < 2 ^ (prefixWord ++ tailWord_859709).sum := by decide
  have hdescent : baseEnd_859709 < baseStart_859709 := by decide
  rcases family_descends (prefixWord ++ tailWord_859709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_859730 : List Nat := [3, 2, 2, 1, 2, 2, 2, 3, 3]
def baseStart_859730 : Nat := 118140960795 + 859730 * 2 ^ 59
def prefixEnd_859730 : Nat := 4983230072969 + 3 ^ 40 * 859730 * 2
def baseEnd_859730 : Nat := 392404198302245809885493

theorem tailTrace_859730 : CollatzResearch.WordTrace tailWord_859730 prefixEnd_859730 392404198302245809885493 := by
  unfold tailWord_859730
  simp only [CollatzResearch.WordTrace]
  refine ⟨7839232293838128759840161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20904619450235010026240429 7839232293838128759840161)
  ·
    refine ⟨5879424220378596569880121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7839232293838128759840161 5879424220378596569880121)
    ·
      refine ⟨4409568165283947427410091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5879424220378596569880121 4409568165283947427410091)
      ·
        refine ⟨6614352247925921141115137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4409568165283947427410091 6614352247925921141115137)
        ·
          refine ⟨4960764185944440855836353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6614352247925921141115137 4960764185944440855836353)
          ·
            refine ⟨3720573139458330641877265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4960764185944440855836353 3720573139458330641877265)
            ·
              refine ⟨2790429854593747981407949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3720573139458330641877265 2790429854593747981407949)
              ·
                refine ⟨1046411195472655493027981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2790429854593747981407949 1046411195472655493027981)
                ·
                  refine ⟨392404198302245809885493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1046411195472655493027981 392404198302245809885493)
                  ·
                    rfl

theorem cell20_859730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 2, 3, 3].length) (baseStart_859730 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_859730 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_859730 prefixEnd_859730 := by exact prefixLift 859730
  have htrace : WordTrace (prefixWord ++ tailWord_859730) baseStart_859730 baseEnd_859730 := by
    simpa [prefixWord, tailWord_859730, baseEnd_859730] using wordTrace_append hprefix tailTrace_859730
  have hstable : (prefixWord ++ tailWord_859730).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_859730).length < 2 ^ (prefixWord ++ tailWord_859730).sum := by decide
  have hdescent : baseEnd_859730 < baseStart_859730 := by decide
  rcases family_descends (prefixWord ++ tailWord_859730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_859754 : List Nat := [3, 1, 3, 2, 1, 2, 1, 5, 2]
def baseStart_859754 : Nat := 118140960795 + 859754 * 2 ^ 59
def prefixEnd_859754 : Nat := 4983230072969 + 3 ^ 40 * 859754 * 2
def baseEnd_859754 : Nat := 392415152556208393085395

theorem tailTrace_859754 : CollatzResearch.WordTrace tailWord_859754 prefixEnd_859754 392415152556208393085395 := by
  unfold tailWord_859754
  simp only [CollatzResearch.WordTrace]
  refine ⟨7839451131816391784558579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20905203018177044758822877 7839451131816391784558579)
  ·
    refine ⟨11759176697724587676837869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7839451131816391784558579 11759176697724587676837869)
    ·
      refine ⟨4409691261646720378814201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11759176697724587676837869 4409691261646720378814201)
      ·
        refine ⟨3307268446235040284110651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4409691261646720378814201 3307268446235040284110651)
        ·
          refine ⟨4960902669352560426165977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3307268446235040284110651 4960902669352560426165977)
          ·
            refine ⟨3720677002014420319624483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4960902669352560426165977 3720677002014420319624483)
            ·
              refine ⟨5581015503021630479436725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3720677002014420319624483 5581015503021630479436725)
              ·
                refine ⟨523220203408277857447193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5581015503021630479436725 523220203408277857447193)
                ·
                  refine ⟨392415152556208393085395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 523220203408277857447193 392415152556208393085395)
                  ·
                    rfl

theorem cell20_859754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 5, 2].length) (baseStart_859754 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_859754 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_859754 prefixEnd_859754 := by exact prefixLift 859754
  have htrace : WordTrace (prefixWord ++ tailWord_859754) baseStart_859754 baseEnd_859754 := by
    simpa [prefixWord, tailWord_859754, baseEnd_859754] using wordTrace_append hprefix tailTrace_859754
  have hstable : (prefixWord ++ tailWord_859754).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_859754).length < 2 ^ (prefixWord ++ tailWord_859754).sum := by decide
  have hdescent : baseEnd_859754 < baseStart_859754 := by decide
  rcases family_descends (prefixWord ++ tailWord_859754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_859799 : List Nat := [1, 1, 3, 3, 2, 4, 2, 4]
def baseStart_859799 : Nat := 118140960795 + 859799 * 2 ^ 59
def prefixEnd_859799 : Nat := 4983230072969 + 3 ^ 40 * 859799 * 2
def baseEnd_859799 : Nat := 130811897260796078861737

theorem tailTrace_859799 : CollatzResearch.WordTrace tailWord_859799 prefixEnd_859799 130811897260796078861737 := by
  unfold tailWord_859799
  simp only [CollatzResearch.WordTrace]
  refine ⟨31359445812102539823622451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20906297208068359882414967 31359445812102539823622451)
  ·
    refine ⟨47039168718153809735433677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31359445812102539823622451 47039168718153809735433677)
    ·
      refine ⟨17639688269307678650787629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47039168718153809735433677 17639688269307678650787629)
      ·
        refine ⟨6614883100990379494045361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17639688269307678650787629 6614883100990379494045361)
        ·
          refine ⟨4961162325742784620534021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6614883100990379494045361 4961162325742784620534021)
          ·
            refine ⟨930217936076772116350129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4961162325742784620534021 930217936076772116350129)
            ·
              refine ⟨697663452057579087262597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 930217936076772116350129 697663452057579087262597)
              ·
                refine ⟨130811897260796078861737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 697663452057579087262597 130811897260796078861737)
                ·
                  rfl

theorem cell20_859799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 2, 4].length) (baseStart_859799 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_859799 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_859799 prefixEnd_859799 := by exact prefixLift 859799
  have htrace : WordTrace (prefixWord ++ tailWord_859799) baseStart_859799 baseEnd_859799 := by
    simpa [prefixWord, tailWord_859799, baseEnd_859799] using wordTrace_append hprefix tailTrace_859799
  have hstable : (prefixWord ++ tailWord_859799).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_859799).length < 2 ^ (prefixWord ++ tailWord_859799).sum := by decide
  have hdescent : baseEnd_859799 < baseStart_859799 := by decide
  rcases family_descends (prefixWord ++ tailWord_859799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_859806 : List Nat := [4, 3, 1, 1, 1, 2, 1, 2, 5]
def baseStart_859806 : Nat := 118140960795 + 859806 * 2 ^ 59
def prefixEnd_859806 : Nat := 4983230072969 + 3 ^ 40 * 859806 * 2
def baseEnd_859806 : Nat := 392438886773127323351849

theorem tailTrace_859806 : CollatzResearch.WordTrace tailWord_859806 prefixEnd_859806 392438886773127323351849 := by
  unfold tailWord_859806
  simp only [CollatzResearch.WordTrace]
  refine ⟨3919962640384647502390909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20906467415384786679418181 3919962640384647502390909)
  ·
    refine ⟨1469985990144242813396591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3919962640384647502390909 1469985990144242813396591)
    ·
      refine ⟨2204978985216364220094887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1469985990144242813396591 2204978985216364220094887)
      ·
        refine ⟨3307468477824546330142331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2204978985216364220094887 3307468477824546330142331)
        ·
          refine ⟨4961202716736819495213497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3307468477824546330142331 4961202716736819495213497)
          ·
            refine ⟨3720902037552614621410123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4961202716736819495213497 3720902037552614621410123)
            ·
              refine ⟨5581353056328921932115185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3720902037552614621410123 5581353056328921932115185)
              ·
                refine ⟨4186014792246691449086389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5581353056328921932115185 4186014792246691449086389)
                ·
                  refine ⟨392438886773127323351849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4186014792246691449086389 392438886773127323351849)
                  ·
                    rfl

theorem cell20_859806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 2, 5].length) (baseStart_859806 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_859806 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_859806 prefixEnd_859806 := by exact prefixLift 859806
  have htrace : WordTrace (prefixWord ++ tailWord_859806) baseStart_859806 baseEnd_859806 := by
    simpa [prefixWord, tailWord_859806, baseEnd_859806] using wordTrace_append hprefix tailTrace_859806
  have hstable : (prefixWord ++ tailWord_859806).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_859806).length < 2 ^ (prefixWord ++ tailWord_859806).sum := by decide
  have hdescent : baseEnd_859806 < baseStart_859806 := by decide
  rcases family_descends (prefixWord ++ tailWord_859806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_859809 : List Nat := [1, 2, 3, 3, 2, 3, 1, 3, 2]
def baseStart_859809 : Nat := 118140960795 + 859809 * 2 ^ 59
def prefixEnd_859809 : Nat := 4983230072969 + 3 ^ 40 * 859809 * 2
def baseEnd_859809 : Nat := 392440256054872646251837

theorem tailTrace_859809 : CollatzResearch.WordTrace tailWord_859809 prefixEnd_859809 392440256054872646251837 := by
  unfold tailWord_859809
  simp only [CollatzResearch.WordTrace]
  refine ⟨31359810542066311531486481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20906540361377541020990987 31359810542066311531486481)
  ·
    refine ⟨23519857906549733648614861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31359810542066311531486481 23519857906549733648614861)
    ·
      refine ⟨8819946714956150118230573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23519857906549733648614861 8819946714956150118230573)
      ·
        refine ⟨3307480018108556294336465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8819946714956150118230573 3307480018108556294336465)
        ·
          refine ⟨2480610013581417220752349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3307480018108556294336465 2480610013581417220752349)
          ·
            refine ⟨930228755093031457782131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2480610013581417220752349 930228755093031457782131)
            ·
              refine ⟨1395343132639547186673197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 930228755093031457782131 1395343132639547186673197)
              ·
                refine ⟨523253674739830195002449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1395343132639547186673197 523253674739830195002449)
                ·
                  refine ⟨392440256054872646251837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 523253674739830195002449 392440256054872646251837)
                  ·
                    rfl

theorem cell20_859809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 1, 3, 2].length) (baseStart_859809 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_859809 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_859809 prefixEnd_859809 := by exact prefixLift 859809
  have htrace : WordTrace (prefixWord ++ tailWord_859809) baseStart_859809 baseEnd_859809 := by
    simpa [prefixWord, tailWord_859809, baseEnd_859809] using wordTrace_append hprefix tailTrace_859809
  have hstable : (prefixWord ++ tailWord_859809).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_859809).length < 2 ^ (prefixWord ++ tailWord_859809).sum := by decide
  have hdescent : baseEnd_859809 < baseStart_859809 := by decide
  rcases family_descends (prefixWord ++ tailWord_859809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_859827 : List Nat := [1, 1, 1, 2, 3, 3, 2, 4, 3]
def baseStart_859827 : Nat := 118140960795 + 859827 * 2 ^ 59
def prefixEnd_859827 : Nat := 4983230072969 + 3 ^ 40 * 859827 * 2
def baseEnd_859827 : Nat := 392448471745344583651763

theorem tailTrace_859827 : CollatzResearch.WordTrace tailWord_859827 prefixEnd_859827 392448471745344583651763 := by
  unfold tailWord_859827
  simp only [CollatzResearch.WordTrace]
  refine ⟨31360467056001100605641735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20906978037334067070427823 31360467056001100605641735)
  ·
    refine ⟨47040700584001650908462603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31360467056001100605641735 47040700584001650908462603)
    ·
      refine ⟨70561050876002476362693905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47040700584001650908462603 70561050876002476362693905)
      ·
        refine ⟨52920788157001857272020429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70561050876002476362693905 52920788157001857272020429)
        ·
          refine ⟨19845295558875696477007661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52920788157001857272020429 19845295558875696477007661)
          ·
            refine ⟨7441985834578386178877873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19845295558875696477007661 7441985834578386178877873)
            ·
              refine ⟨5581489375933789634158405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7441985834578386178877873 5581489375933789634158405)
              ·
                refine ⟨1046529257987585556404701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5581489375933789634158405 1046529257987585556404701)
                ·
                  refine ⟨392448471745344583651763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1046529257987585556404701 392448471745344583651763)
                  ·
                    rfl

theorem cell20_859827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 4, 3].length) (baseStart_859827 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_859827 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_859827 prefixEnd_859827 := by exact prefixLift 859827
  have htrace : WordTrace (prefixWord ++ tailWord_859827) baseStart_859827 baseEnd_859827 := by
    simpa [prefixWord, tailWord_859827, baseEnd_859827] using wordTrace_append hprefix tailTrace_859827
  have hstable : (prefixWord ++ tailWord_859827).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_859827).length < 2 ^ (prefixWord ++ tailWord_859827).sum := by decide
  have hdescent : baseEnd_859827 < baseStart_859827 := by decide
  rcases family_descends (prefixWord ++ tailWord_859827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_859844 : List Nat := [2, 3, 3, 1, 1, 1, 3, 3, 3]
def baseStart_859844 : Nat := 118140960795 + 859844 * 2 ^ 59
def prefixEnd_859844 : Nat := 4983230072969 + 3 ^ 40 * 859844 * 2
def baseEnd_859844 : Nat := 392456231008568080085027

theorem tailTrace_859844 : CollatzResearch.WordTrace tailWord_859844 prefixEnd_859844 392456231008568080085027 := by
  unfold tailWord_859844
  simp only [CollatzResearch.WordTrace]
  refine ⟨15680543548469756254505293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20907391397959675006007057 15680543548469756254505293)
  ·
    refine ⟨5880203830676158595439485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15680543548469756254505293 5880203830676158595439485)
    ·
      refine ⟨2205076436503559473289807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5880203830676158595439485 2205076436503559473289807)
      ·
        refine ⟨3307614654755339209934711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2205076436503559473289807 3307614654755339209934711)
        ·
          refine ⟨4961421982133008814902067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3307614654755339209934711 4961421982133008814902067)
          ·
            refine ⟨7442132973199513222353101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4961421982133008814902067 7442132973199513222353101)
            ·
              refine ⟨2790799864949817458382413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7442132973199513222353101 2790799864949817458382413)
              ·
                refine ⟨1046549949356181546893405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2790799864949817458382413 1046549949356181546893405)
                ·
                  refine ⟨392456231008568080085027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1046549949356181546893405 392456231008568080085027)
                  ·
                    rfl

theorem cell20_859844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 3, 3, 3].length) (baseStart_859844 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_859844 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_859844 prefixEnd_859844 := by exact prefixLift 859844
  have htrace : WordTrace (prefixWord ++ tailWord_859844) baseStart_859844 baseEnd_859844 := by
    simpa [prefixWord, tailWord_859844, baseEnd_859844] using wordTrace_append hprefix tailTrace_859844
  have hstable : (prefixWord ++ tailWord_859844).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_859844).length < 2 ^ (prefixWord ++ tailWord_859844).sum := by decide
  have hdescent : baseEnd_859844 < baseStart_859844 := by decide
  rcases family_descends (prefixWord ++ tailWord_859844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_859858 : List Nat := [3, 2, 2, 2, 2, 1, 2, 6]
def baseStart_859858 : Nat := 118140960795 + 859858 * 2 ^ 59
def prefixEnd_859858 : Nat := 4983230072969 + 3 ^ 40 * 859858 * 2
def baseEnd_859858 : Nat := 130820873663348751206101

theorem tailTrace_859858 : CollatzResearch.WordTrace tailWord_859858 prefixEnd_859858 130820873663348751206101 := by
  unfold tailWord_859858
  simp only [CollatzResearch.WordTrace]
  refine ⟨7840399429722198225005057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20907731812592528600013485 7840399429722198225005057)
  ·
    refine ⟨5880299572291648668753793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7840399429722198225005057 5880299572291648668753793)
    ·
      refine ⟨4410224679218736501565345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5880299572291648668753793 4410224679218736501565345)
      ·
        refine ⟨3307668509414052376174009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4410224679218736501565345 3307668509414052376174009)
        ·
          refine ⟨2480751382060539282130507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3307668509414052376174009 2480751382060539282130507)
          ·
            refine ⟨3721127073090808923195761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2480751382060539282130507 3721127073090808923195761)
            ·
              refine ⟨2790845304818106692396821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3721127073090808923195761 2790845304818106692396821)
              ·
                refine ⟨130820873663348751206101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2790845304818106692396821 130820873663348751206101)
                ·
                  rfl

theorem cell20_859858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 2, 6].length) (baseStart_859858 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_859858 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_859858 prefixEnd_859858 := by exact prefixLift 859858
  have htrace : WordTrace (prefixWord ++ tailWord_859858) baseStart_859858 baseEnd_859858 := by
    simpa [prefixWord, tailWord_859858, baseEnd_859858] using wordTrace_append hprefix tailTrace_859858
  have hstable : (prefixWord ++ tailWord_859858).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_859858).length < 2 ^ (prefixWord ++ tailWord_859858).sum := by decide
  have hdescent : baseEnd_859858 < baseStart_859858 := by decide
  rcases family_descends (prefixWord ++ tailWord_859858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_859885 : List Nat := [1, 5, 1, 2, 1, 2, 4, 2, 2]
def baseStart_859885 : Nat := 118140960795 + 859885 * 2 ^ 59
def prefixEnd_859885 : Nat := 4983230072969 + 3 ^ 40 * 859885 * 2
def baseEnd_859885 : Nat := 392474944525754159718193

theorem tailTrace_859885 : CollatzResearch.WordTrace tailWord_859885 prefixEnd_859885 392474944525754159718193 := by
  unfold tailWord_859885
  simp only [CollatzResearch.WordTrace]
  refine ⟨31362582489790976511253109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20908388326527317674168739 31362582489790976511253109)
  ·
    refine ⟨2940242108417904047929979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 31362582489790976511253109 2940242108417904047929979)
    ·
      refine ⟨4410363162626856071894969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2940242108417904047929979 4410363162626856071894969)
      ·
        refine ⟨3307772371970142053921227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4410363162626856071894969 3307772371970142053921227)
        ·
          refine ⟨4961658557955213080881841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3307772371970142053921227 4961658557955213080881841)
          ·
            refine ⟨3721243918466409810661381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4961658557955213080881841 3721243918466409810661381)
            ·
              refine ⟨697733234712451839499009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3721243918466409810661381 697733234712451839499009)
              ·
                refine ⟨523299926034338879624257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 697733234712451839499009 523299926034338879624257)
                ·
                  refine ⟨392474944525754159718193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 523299926034338879624257 392474944525754159718193)
                  ·
                    rfl

theorem cell20_859885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 4, 2, 2].length) (baseStart_859885 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_859885 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_859885 prefixEnd_859885 := by exact prefixLift 859885
  have htrace : WordTrace (prefixWord ++ tailWord_859885) baseStart_859885 baseEnd_859885 := by
    simpa [prefixWord, tailWord_859885, baseEnd_859885] using wordTrace_append hprefix tailTrace_859885
  have hstable : (prefixWord ++ tailWord_859885).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_859885).length < 2 ^ (prefixWord ++ tailWord_859885).sum := by decide
  have hdescent : baseEnd_859885 < baseStart_859885 := by decide
  rcases family_descends (prefixWord ++ tailWord_859885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_859892 : List Nat := [2, 6, 1, 1, 1, 1, 3, 5]
def baseStart_859892 : Nat := 118140960795 + 859892 * 2 ^ 59
def prefixEnd_859892 : Nat := 4983230072969 + 3 ^ 40 * 859892 * 2
def baseEnd_859892 : Nat := 130826046505497748828277

theorem tailTrace_859892 : CollatzResearch.WordTrace tailWord_859892 prefixEnd_859892 130826046505497748828277 := by
  unfold tailWord_859892
  simp only [CollatzResearch.WordTrace]
  refine ⟨15681418900382808353378965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20908558533843744471171953 15681418900382808353378965)
  ·
    refine ⟨735066510955444141564639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 15681418900382808353378965 735066510955444141564639)
    ·
      refine ⟨1102599766433166212346959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 735066510955444141564639 1102599766433166212346959)
      ·
        refine ⟨1653899649649749318520439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1102599766433166212346959 1653899649649749318520439)
        ·
          refine ⟨2480849474474623977780659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1653899649649749318520439 2480849474474623977780659)
          ·
            refine ⟨3721274211711935966670989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2480849474474623977780659 3721274211711935966670989)
            ·
              refine ⟨1395477829391975987501621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3721274211711935966670989 1395477829391975987501621)
              ·
                refine ⟨130826046505497748828277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1395477829391975987501621 130826046505497748828277)
                ·
                  rfl

theorem cell20_859892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 3, 5].length) (baseStart_859892 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_859892 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_859892 prefixEnd_859892 := by exact prefixLift 859892
  have htrace : WordTrace (prefixWord ++ tailWord_859892) baseStart_859892 baseEnd_859892 := by
    simpa [prefixWord, tailWord_859892, baseEnd_859892] using wordTrace_append hprefix tailTrace_859892
  have hstable : (prefixWord ++ tailWord_859892).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_859892).length < 2 ^ (prefixWord ++ tailWord_859892).sum := by decide
  have hdescent : baseEnd_859892 < baseStart_859892 := by decide
  rcases family_descends (prefixWord ++ tailWord_859892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_859903 : List Nat := [1, 1, 2, 2, 1, 3, 4, 3, 3]
def baseStart_859903 : Nat := 118140960795 + 859903 * 2 ^ 59
def prefixEnd_859903 : Nat := 4983230072969 + 3 ^ 40 * 859903 * 2
def baseEnd_859903 : Nat := 392483160216226097118119

theorem tailTrace_859903 : CollatzResearch.WordTrace tailWord_859903 prefixEnd_859903 392483160216226097118119 := by
  unfold tailWord_859903
  simp only [CollatzResearch.WordTrace]
  refine ⟨31363239003725765585408363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20908826002483843723605575 31363239003725765585408363)
  ·
    refine ⟨47044858505588648378112545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31363239003725765585408363 47044858505588648378112545)
    ·
      refine ⟨35283643879191486283584409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47044858505588648378112545 35283643879191486283584409)
      ·
        refine ⟨26462732909393614712688307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35283643879191486283584409 26462732909393614712688307)
        ·
          refine ⟨39694099364090422069032461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26462732909393614712688307 39694099364090422069032461)
          ·
            refine ⟨14885287261533908275887173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39694099364090422069032461 14885287261533908275887173)
            ·
              refine ⟨2790991361537607801728845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14885287261533908275887173 2790991361537607801728845)
              ·
                refine ⟨1046621760576602925648317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2790991361537607801728845 1046621760576602925648317)
                ·
                  refine ⟨392483160216226097118119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1046621760576602925648317 392483160216226097118119)
                  ·
                    rfl

theorem cell20_859903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 4, 3, 3].length) (baseStart_859903 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_859903 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_859903 prefixEnd_859903 := by exact prefixLift 859903
  have htrace : WordTrace (prefixWord ++ tailWord_859903) baseStart_859903 baseEnd_859903 := by
    simpa [prefixWord, tailWord_859903, baseEnd_859903] using wordTrace_append hprefix tailTrace_859903
  have hstable : (prefixWord ++ tailWord_859903).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_859903).length < 2 ^ (prefixWord ++ tailWord_859903).sum := by decide
  have hdescent : baseEnd_859903 < baseStart_859903 := by decide
  rcases family_descends (prefixWord ++ tailWord_859903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_859941 : List Nat := [1, 3, 1, 2, 3, 3, 1, 1, 5]
def baseStart_859941 : Nat := 118140960795 + 859941 * 2 ^ 59
def prefixEnd_859941 : Nat := 4983230072969 + 3 ^ 40 * 859941 * 2
def baseEnd_859941 : Nat := 392500504451666853851297

theorem tailTrace_859941 : CollatzResearch.WordTrace tailWord_859941 prefixEnd_859941 392500504451666853851297 := by
  unfold tailWord_859941
  simp only [CollatzResearch.WordTrace]
  refine ⟨31364624977588098075291677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20909749985058732050194451 31364624977588098075291677)
  ·
    refine ⟨11761734366595536778234379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31364624977588098075291677 11761734366595536778234379)
    ·
      refine ⟨17642601549893305167351569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11761734366595536778234379 17642601549893305167351569)
      ·
        refine ⟨13231951162419978875513677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17642601549893305167351569 13231951162419978875513677)
        ·
          refine ⟨4961981685907492078317629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13231951162419978875513677 4961981685907492078317629)
          ·
            refine ⟨1860743132215309529369111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4961981685907492078317629 1860743132215309529369111)
            ·
              refine ⟨2791114698322964294053667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1860743132215309529369111 2791114698322964294053667)
              ·
                refine ⟨4186672047484446441080501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2791114698322964294053667 4186672047484446441080501)
                ·
                  refine ⟨392500504451666853851297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4186672047484446441080501 392500504451666853851297)
                  ·
                    rfl

theorem cell20_859941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 1, 1, 5].length) (baseStart_859941 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_859941 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_859941 prefixEnd_859941 := by exact prefixLift 859941
  have htrace : WordTrace (prefixWord ++ tailWord_859941) baseStart_859941 baseEnd_859941 := by
    simpa [prefixWord, tailWord_859941, baseEnd_859941] using wordTrace_append hprefix tailTrace_859941
  have hstable : (prefixWord ++ tailWord_859941).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_859941).length < 2 ^ (prefixWord ++ tailWord_859941).sum := by decide
  have hdescent : baseEnd_859941 < baseStart_859941 := by decide
  rcases family_descends (prefixWord ++ tailWord_859941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_859944 : List Nat := [2, 1, 5, 1, 1, 2, 2, 4, 2]
def baseStart_859944 : Nat := 118140960795 + 859944 * 2 ^ 59
def prefixEnd_859944 : Nat := 4983230072969 + 3 ^ 40 * 859944 * 2
def baseEnd_859944 : Nat := 392501873733412176751285

theorem tailTrace_859944 : CollatzResearch.WordTrace tailWord_859944 prefixEnd_859944 392501873733412176751285 := by
  unfold tailWord_859944
  simp only [CollatzResearch.WordTrace]
  refine ⟨15682367198288614793825443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20909822931051486391767257 15682367198288614793825443)
  ·
    refine ⟨23523550797432922190738165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15682367198288614793825443 23523550797432922190738165)
    ·
      refine ⟨2205332887259336455381703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 23523550797432922190738165 2205332887259336455381703)
      ·
        refine ⟨3307999330889004683072555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2205332887259336455381703 3307999330889004683072555)
        ·
          refine ⟨4961998996333507024608833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3307999330889004683072555 4961998996333507024608833)
          ·
            refine ⟨3721499247250130268456625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4961998996333507024608833 3721499247250130268456625)
            ·
              refine ⟨2791124435437597701342469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3721499247250130268456625 2791124435437597701342469)
              ·
                refine ⟨523335831644549569001713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2791124435437597701342469 523335831644549569001713)
                ·
                  refine ⟨392501873733412176751285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 523335831644549569001713 392501873733412176751285)
                  ·
                    rfl

theorem cell20_859944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 2, 4, 2].length) (baseStart_859944 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_859944 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_859944 prefixEnd_859944 := by exact prefixLift 859944
  have htrace : WordTrace (prefixWord ++ tailWord_859944) baseStart_859944 baseEnd_859944 := by
    simpa [prefixWord, tailWord_859944, baseEnd_859944] using wordTrace_append hprefix tailTrace_859944
  have hstable : (prefixWord ++ tailWord_859944).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_859944).length < 2 ^ (prefixWord ++ tailWord_859944).sum := by decide
  have hdescent : baseEnd_859944 < baseStart_859944 := by decide
  rcases family_descends (prefixWord ++ tailWord_859944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_859948 : List Nat := [2, 2, 1, 1, 1, 5, 1, 3, 4]
def baseStart_859948 : Nat := 118140960795 + 859948 * 2 ^ 59
def prefixEnd_859948 : Nat := 4983230072969 + 3 ^ 40 * 859948 * 2
def baseEnd_859948 : Nat := 392503699442405940617935

theorem tailTrace_859948 : CollatzResearch.WordTrace tailWord_859948 prefixEnd_859948 392503699442405940617935 := by
  unfold tailWord_859948
  simp only [CollatzResearch.WordTrace]
  refine ⟨15682440144281369135398249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20909920192375158847197665 15682440144281369135398249)
  ·
    refine ⟨11761830108211026851548687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15682440144281369135398249 11761830108211026851548687)
    ·
      refine ⟨17642745162316540277323031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11761830108211026851548687 17642745162316540277323031)
      ·
        refine ⟨26464117743474810415984547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17642745162316540277323031 26464117743474810415984547)
        ·
          refine ⟨39696176615212215623976821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26464117743474810415984547 39696176615212215623976821)
          ·
            refine ⟨3721516557676145214747827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 39696176615212215623976821 3721516557676145214747827)
            ·
              refine ⟨5582274836514217822121741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3721516557676145214747827 5582274836514217822121741)
              ·
                refine ⟨2093353063692831683295653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5582274836514217822121741 2093353063692831683295653)
                ·
                  refine ⟨392503699442405940617935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2093353063692831683295653 392503699442405940617935)
                  ·
                    rfl

theorem cell20_859948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 4].length) (baseStart_859948 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_859948 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_859948 prefixEnd_859948 := by exact prefixLift 859948
  have htrace : WordTrace (prefixWord ++ tailWord_859948) baseStart_859948 baseEnd_859948 := by
    simpa [prefixWord, tailWord_859948, baseEnd_859948] using wordTrace_append hprefix tailTrace_859948
  have hstable : (prefixWord ++ tailWord_859948).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_859948).length < 2 ^ (prefixWord ++ tailWord_859948).sum := by decide
  have hdescent : baseEnd_859948 < baseStart_859948 := by decide
  rcases family_descends (prefixWord ++ tailWord_859948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_859965 : List Nat := [1, 4, 1, 4, 1, 1, 2, 2, 4]
def baseStart_859965 : Nat := 118140960795 + 859965 * 2 ^ 59
def prefixEnd_859965 : Nat := 4983230072969 + 3 ^ 40 * 859965 * 2
def baseEnd_859965 : Nat := 392511458705629437051199

theorem tailTrace_859965 : CollatzResearch.WordTrace tailWord_859965 prefixEnd_859965 392511458705629437051199 := by
  unfold tailWord_859965
  simp only [CollatzResearch.WordTrace]
  refine ⟨31365500329501150174165349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20910333553000766782776899 31365500329501150174165349)
  ·
    refine ⟨5881031311781465657656003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31365500329501150174165349 5881031311781465657656003)
    ·
      refine ⟨8821546967672198486484005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5881031311781465657656003 8821546967672198486484005)
      ·
        refine ⟨1654040056438537216215751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8821546967672198486484005 1654040056438537216215751)
        ·
          refine ⟨2481060084657805824323627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1654040056438537216215751 2481060084657805824323627)
          ·
            refine ⟨3721590126986708736485441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2481060084657805824323627 3721590126986708736485441)
            ·
              refine ⟨2791192595240031552364081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3721590126986708736485441 2791192595240031552364081)
              ·
                refine ⟨2093394446430023664273061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2791192595240031552364081 2093394446430023664273061)
                ·
                  refine ⟨392511458705629437051199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2093394446430023664273061 392511458705629437051199)
                  ·
                    rfl

theorem cell20_859965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 2, 2, 4].length) (baseStart_859965 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_859965 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_859965 prefixEnd_859965 := by exact prefixLift 859965
  have htrace : WordTrace (prefixWord ++ tailWord_859965) baseStart_859965 baseEnd_859965 := by
    simpa [prefixWord, tailWord_859965, baseEnd_859965] using wordTrace_append hprefix tailTrace_859965
  have hstable : (prefixWord ++ tailWord_859965).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_859965).length < 2 ^ (prefixWord ++ tailWord_859965).sum := by decide
  have hdescent : baseEnd_859965 < baseStart_859965 := by decide
  rcases family_descends (prefixWord ++ tailWord_859965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_860017 : List Nat := [1, 2, 2, 2, 1, 3, 3, 3, 3]
def baseStart_860017 : Nat := 118140960795 + 860017 * 2 ^ 59
def prefixEnd_860017 : Nat := 4983230072969 + 3 ^ 40 * 860017 * 2
def baseEnd_860017 : Nat := 392535192922548367317653

theorem tailTrace_860017 : CollatzResearch.WordTrace tailWord_860017 prefixEnd_860017 392535192922548367317653 := by
  unfold tailWord_860017
  simp only [CollatzResearch.WordTrace]
  refine ⟨31367396925312763055058305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20911597950208508703372203 31367396925312763055058305)
  ·
    refine ⟨23525547693984572291293729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31367396925312763055058305 23525547693984572291293729)
    ·
      refine ⟨17644160770488429218470297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23525547693984572291293729 17644160770488429218470297)
      ·
        refine ⟨13233120577866321913852723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17644160770488429218470297 13233120577866321913852723)
        ·
          refine ⟨19849680866799482870779085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13233120577866321913852723 19849680866799482870779085)
          ·
            refine ⟨7443630325049806076542157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19849680866799482870779085 7443630325049806076542157)
            ·
              refine ⟨2791361371893677278703309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7443630325049806076542157 2791361371893677278703309)
              ·
                refine ⟨1046760514460128979513741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2791361371893677278703309 1046760514460128979513741)
                ·
                  refine ⟨392535192922548367317653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1046760514460128979513741 392535192922548367317653)
                  ·
                    rfl

theorem cell20_860017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 3, 3, 3].length) (baseStart_860017 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_860017 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_860017 prefixEnd_860017 := by exact prefixLift 860017
  have htrace : WordTrace (prefixWord ++ tailWord_860017) baseStart_860017 baseEnd_860017 := by
    simpa [prefixWord, tailWord_860017, baseEnd_860017] using wordTrace_append hprefix tailTrace_860017
  have hstable : (prefixWord ++ tailWord_860017).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_860017).length < 2 ^ (prefixWord ++ tailWord_860017).sum := by decide
  have hdescent : baseEnd_860017 < baseStart_860017 := by decide
  rcases family_descends (prefixWord ++ tailWord_860017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_860041 : List Nat := [1, 2, 1, 1, 5, 1, 2, 5, 2]
def baseStart_860041 : Nat := 118140960795 + 860041 * 2 ^ 59
def prefixEnd_860041 : Nat := 4983230072969 + 3 ^ 40 * 860041 * 2
def baseEnd_860041 : Nat := 392546147176510950517555

theorem tailTrace_860041 : CollatzResearch.WordTrace tailWord_860041 prefixEnd_860041 392546147176510950517555 := by
  unfold tailWord_860041
  simp only [CollatzResearch.WordTrace]
  refine ⟨31368272277225815153931977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20912181518150543435954651 31368272277225815153931977)
  ·
    refine ⟨23526204207919361365448983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31368272277225815153931977 23526204207919361365448983)
    ·
      refine ⟨35289306311879042048173475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23526204207919361365448983 35289306311879042048173475)
      ·
        refine ⟨52933959467818563072260213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35289306311879042048173475 52933959467818563072260213)
        ·
          refine ⟨4962558700107990288024395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 52933959467818563072260213 4962558700107990288024395)
          ·
            refine ⟨7443838050161985432036593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4962558700107990288024395 7443838050161985432036593)
            ·
              refine ⟨5582878537621489074027445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7443838050161985432036593 5582878537621489074027445)
              ·
                refine ⟨523394862902014600690073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5582878537621489074027445 523394862902014600690073)
                ·
                  refine ⟨392546147176510950517555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 523394862902014600690073 392546147176510950517555)
                  ·
                    rfl

theorem cell20_860041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 5, 2].length) (baseStart_860041 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_860041 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_860041 prefixEnd_860041 := by exact prefixLift 860041
  have htrace : WordTrace (prefixWord ++ tailWord_860041) baseStart_860041 baseEnd_860041 := by
    simpa [prefixWord, tailWord_860041, baseEnd_860041] using wordTrace_append hprefix tailTrace_860041
  have hstable : (prefixWord ++ tailWord_860041).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_860041).length < 2 ^ (prefixWord ++ tailWord_860041).sum := by decide
  have hdescent : baseEnd_860041 < baseStart_860041 := by decide
  rcases family_descends (prefixWord ++ tailWord_860041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_860055 : List Nat := [1, 1, 3, 3, 1, 3, 1, 4, 3]
def baseStart_860055 : Nat := 118140960795 + 860055 * 2 ^ 59
def prefixEnd_860055 : Nat := 4983230072969 + 3 ^ 40 * 860055 * 2
def baseEnd_860055 : Nat := 392552537157989124050831

theorem tailTrace_860055 : CollatzResearch.WordTrace tailWord_860055 prefixEnd_860055 392552537157989124050831 := by
  unfold tailWord_860055
  simp only [CollatzResearch.WordTrace]
  refine ⟨31368782899175095544941619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20912521932783397029961079 31368782899175095544941619)
  ·
    refine ⟨47053174348762643317412429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31368782899175095544941619 47053174348762643317412429)
    ·
      refine ⟨17644940380785991244029661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47053174348762643317412429 17644940380785991244029661)
      ·
        refine ⟨6616852642794746716511123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17644940380785991244029661 6616852642794746716511123)
        ·
          refine ⟨9925278964192120074766685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6616852642794746716511123 9925278964192120074766685)
          ·
            refine ⟨3721979611572045028037507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9925278964192120074766685 3721979611572045028037507)
            ·
              refine ⟨5582969417358067542056261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3721979611572045028037507 5582969417358067542056261)
              ·
                refine ⟨1046806765754637664135549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5582969417358067542056261 1046806765754637664135549)
                ·
                  refine ⟨392552537157989124050831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1046806765754637664135549 392552537157989124050831)
                  ·
                    rfl

theorem cell20_860055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 4, 3].length) (baseStart_860055 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_860055 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_860055 prefixEnd_860055 := by exact prefixLift 860055
  have htrace : WordTrace (prefixWord ++ tailWord_860055) baseStart_860055 baseEnd_860055 := by
    simpa [prefixWord, tailWord_860055, baseEnd_860055] using wordTrace_append hprefix tailTrace_860055
  have hstable : (prefixWord ++ tailWord_860055).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_860055).length < 2 ^ (prefixWord ++ tailWord_860055).sum := by decide
  have hdescent : baseEnd_860055 < baseStart_860055 := by decide
  rcases family_descends (prefixWord ++ tailWord_860055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_860058 : List Nat := [3, 1, 1, 4, 2, 2, 1, 4, 2]
def baseStart_860058 : Nat := 118140960795 + 860058 * 2 ^ 59
def prefixEnd_860058 : Nat := 4983230072969 + 3 ^ 40 * 860058 * 2
def baseEnd_860058 : Nat := 392553906439734446950819

theorem tailTrace_860058 : CollatzResearch.WordTrace tailWord_860058 prefixEnd_860058 392553906439734446950819 := by
  unfold tailWord_860058
  simp only [CollatzResearch.WordTrace]
  refine ⟨7842223079541056764325207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20912594878776151371533885 7842223079541056764325207)
  ·
    refine ⟨11763334619311585146487811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7842223079541056764325207 11763334619311585146487811)
    ·
      refine ⟨17645001928967377719731717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11763334619311585146487811 17645001928967377719731717)
      ·
        refine ⟨3308437861681383322449697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17645001928967377719731717 3308437861681383322449697)
        ·
          refine ⟨2481328396261037491837273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3308437861681383322449697 2481328396261037491837273)
          ·
            refine ⟨1860996297195778118877955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2481328396261037491837273 1860996297195778118877955)
            ·
              refine ⟨2791494445793667178316933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1860996297195778118877955 2791494445793667178316933)
              ·
                refine ⟨523405208586312595934425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2791494445793667178316933 523405208586312595934425)
                ·
                  refine ⟨392553906439734446950819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 523405208586312595934425 392553906439734446950819)
                  ·
                    rfl

theorem cell20_860058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 1, 4, 2].length) (baseStart_860058 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_860058 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_860058 prefixEnd_860058 := by exact prefixLift 860058
  have htrace : WordTrace (prefixWord ++ tailWord_860058) baseStart_860058 baseEnd_860058 := by
    simpa [prefixWord, tailWord_860058, baseEnd_860058] using wordTrace_append hprefix tailTrace_860058
  have hstable : (prefixWord ++ tailWord_860058).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_860058).length < 2 ^ (prefixWord ++ tailWord_860058).sum := by decide
  have hdescent : baseEnd_860058 < baseStart_860058 := by decide
  rcases family_descends (prefixWord ++ tailWord_860058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_860065 : List Nat := [1, 2, 3, 4, 2, 2, 1, 5]
def baseStart_860065 : Nat := 118140960795 + 860065 * 2 ^ 59
def prefixEnd_860065 : Nat := 4983230072969 + 3 ^ 40 * 860065 * 2
def baseEnd_860065 : Nat := 130852367143491177905819

theorem tailTrace_860065 : CollatzResearch.WordTrace tailWord_860065 prefixEnd_860065 130852367143491177905819 := by
  unfold tailWord_860065
  simp only [CollatzResearch.WordTrace]
  refine ⟨31369147629138867252805649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20912765086092578168537099 31369147629138867252805649)
  ·
    refine ⟨23526860721854150439604237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31369147629138867252805649 23526860721854150439604237)
    ·
      refine ⟨8822572770695306414851589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23526860721854150439604237 8822572770695306414851589)
      ·
        refine ⟨1654232394505369952784673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8822572770695306414851589 1654232394505369952784673)
        ·
          refine ⟨1240674295879027464588505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1654232394505369952784673 1240674295879027464588505)
          ·
            refine ⟨930505721909270598441379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1240674295879027464588505 930505721909270598441379)
            ·
              refine ⟨1395758582863905897662069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 930505721909270598441379 1395758582863905897662069)
              ·
                refine ⟨130852367143491177905819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1395758582863905897662069 130852367143491177905819)
                ·
                  rfl

theorem cell20_860065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 1, 5].length) (baseStart_860065 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_860065 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_860065 prefixEnd_860065 := by exact prefixLift 860065
  have htrace : WordTrace (prefixWord ++ tailWord_860065) baseStart_860065 baseEnd_860065 := by
    simpa [prefixWord, tailWord_860065, baseEnd_860065] using wordTrace_append hprefix tailTrace_860065
  have hstable : (prefixWord ++ tailWord_860065).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_860065).length < 2 ^ (prefixWord ++ tailWord_860065).sum := by decide
  have hdescent : baseEnd_860065 < baseStart_860065 := by decide
  rcases family_descends (prefixWord ++ tailWord_860065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_860117 : List Nat := [1, 3, 2, 3, 2, 2, 2, 1, 4]
def baseStart_860117 : Nat := 118140960795 + 860117 * 2 ^ 59
def prefixEnd_860117 : Nat := 4983230072969 + 3 ^ 40 * 860117 * 2
def baseEnd_860117 : Nat := 392580835647392463983911

theorem tailTrace_860117 : CollatzResearch.WordTrace tailWord_860117 prefixEnd_860117 392580835647392463983911 := by
  unfold tailWord_860117
  simp only [CollatzResearch.WordTrace]
  refine ⟨31371044224950480133698605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20914029483300320089132403 31371044224950480133698605)
  ·
    refine ⟨11764141584356430050136977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31371044224950480133698605 11764141584356430050136977)
    ·
      refine ⟨8823106188267322537602733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11764141584356430050136977 8823106188267322537602733)
      ·
        refine ⟨3308664820600245951601025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8823106188267322537602733 3308664820600245951601025)
        ·
          refine ⟨2481498615450184463700769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3308664820600245951601025 2481498615450184463700769)
          ·
            refine ⟨1861123961587638347775577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2481498615450184463700769 1861123961587638347775577)
            ·
              refine ⟨1395842971190728760831683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1861123961587638347775577 1395842971190728760831683)
              ·
                refine ⟨2093764456786093141247525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1395842971190728760831683 2093764456786093141247525)
                ·
                  refine ⟨392580835647392463983911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2093764456786093141247525 392580835647392463983911)
                  ·
                    rfl

theorem cell20_860117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 2, 1, 4].length) (baseStart_860117 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_860117 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_860117 prefixEnd_860117 := by exact prefixLift 860117
  have htrace : WordTrace (prefixWord ++ tailWord_860117) baseStart_860117 baseEnd_860117 := by
    simpa [prefixWord, tailWord_860117, baseEnd_860117] using wordTrace_append hprefix tailTrace_860117
  have hstable : (prefixWord ++ tailWord_860117).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_860117).length < 2 ^ (prefixWord ++ tailWord_860117).sum := by decide
  have hdescent : baseEnd_860117 < baseStart_860117 := by decide
  rcases family_descends (prefixWord ++ tailWord_860117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_860138 : List Nat := [3, 1, 3, 1, 2, 1, 1, 4, 4]
def baseStart_860138 : Nat := 118140960795 + 860138 * 2 ^ 59
def prefixEnd_860138 : Nat := 4983230072969 + 3 ^ 40 * 860138 * 2
def baseEnd_860138 : Nat := 392590420619609724283825

theorem tailTrace_860138 : CollatzResearch.WordTrace tailWord_860138 prefixEnd_860138 392590420619609724283825 := by
  unfold tailWord_860138
  simp only [CollatzResearch.WordTrace]
  refine ⟨7842952539468600180053267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20914540105249600480142045 7842952539468600180053267)
  ·
    refine ⟨11764428809202900270079901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7842952539468600180053267 11764428809202900270079901)
    ·
      refine ⟨4411660803451087601279963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11764428809202900270079901 4411660803451087601279963)
      ·
        refine ⟨6617491205176631401919945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4411660803451087601279963 6617491205176631401919945)
        ·
          refine ⟨4963118403882473551439959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6617491205176631401919945 4963118403882473551439959)
          ·
            refine ⟨7444677605823710327159939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4963118403882473551439959 7444677605823710327159939)
            ·
              refine ⟨11167016408735565490739909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7444677605823710327159939 11167016408735565490739909)
              ·
                refine ⟨2093815576637918529513733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11167016408735565490739909 2093815576637918529513733)
                ·
                  refine ⟨392590420619609724283825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2093815576637918529513733 392590420619609724283825)
                  ·
                    rfl

theorem cell20_860138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 4, 4].length) (baseStart_860138 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_860138 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_860138 prefixEnd_860138 := by exact prefixLift 860138
  have htrace : WordTrace (prefixWord ++ tailWord_860138) baseStart_860138 baseEnd_860138 := by
    simpa [prefixWord, tailWord_860138, baseEnd_860138] using wordTrace_append hprefix tailTrace_860138
  have hstable : (prefixWord ++ tailWord_860138).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_860138).length < 2 ^ (prefixWord ++ tailWord_860138).sum := by decide
  have hdescent : baseEnd_860138 < baseStart_860138 := by decide
  rcases family_descends (prefixWord ++ tailWord_860138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_860141 : List Nat := [1, 5, 1, 4, 1, 1, 1, 6]
def baseStart_860141 : Nat := 118140960795 + 860141 * 2 ^ 59
def prefixEnd_860141 : Nat := 4983230072969 + 3 ^ 40 * 860141 * 2
def baseEnd_860141 : Nat := 130863929967118349061271

theorem tailTrace_860141 : CollatzResearch.WordTrace tailWord_860141 prefixEnd_860141 130863929967118349061271 := by
  unfold tailWord_860141
  simp only [CollatzResearch.WordTrace]
  refine ⟨31371919576863532232572277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20914613051242354821714851 31371919576863532232572277)
  ·
    refine ⟨2941117460330956146803651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 31371919576863532232572277 2941117460330956146803651)
    ·
      refine ⟨4411676190496434220205477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2941117460330956146803651 4411676190496434220205477)
      ·
        refine ⟨827189285718081416288527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4411676190496434220205477 827189285718081416288527)
        ·
          refine ⟨1240783928577122124432791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 827189285718081416288527 1240783928577122124432791)
          ·
            refine ⟨1861175892865683186649187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1240783928577122124432791 1861175892865683186649187)
            ·
              refine ⟨2791763839298524779973781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1861175892865683186649187 2791763839298524779973781)
              ·
                refine ⟨130863929967118349061271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2791763839298524779973781 130863929967118349061271)
                ·
                  rfl

theorem cell20_860141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 1, 6].length) (baseStart_860141 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_860141 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_860141 prefixEnd_860141 := by exact prefixLift 860141
  have htrace : WordTrace (prefixWord ++ tailWord_860141) baseStart_860141 baseEnd_860141 := by
    simpa [prefixWord, tailWord_860141, baseEnd_860141] using wordTrace_append hprefix tailTrace_860141
  have hstable : (prefixWord ++ tailWord_860141).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_860141).length < 2 ^ (prefixWord ++ tailWord_860141).sum := by decide
  have hdescent : baseEnd_860141 < baseStart_860141 := by decide
  rcases family_descends (prefixWord ++ tailWord_860141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_860152 : List Nat := [2, 1, 2, 1, 1, 3, 3, 2, 5]
def baseStart_860152 : Nat := 118140960795 + 860152 * 2 ^ 59
def prefixEnd_860152 : Nat := 4983230072969 + 3 ^ 40 * 860152 * 2
def baseEnd_860152 : Nat := 392596810601087897817101

theorem tailTrace_860152 : CollatzResearch.WordTrace tailWord_860152 prefixEnd_860152 392596810601087897817101 := by
  unfold tailWord_860152
  simp only [CollatzResearch.WordTrace]
  refine ⟨15686160389911840555611355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20914880519882454074148473 15686160389911840555611355)
  ·
    refine ⟨23529240584867760833417033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15686160389911840555611355 23529240584867760833417033)
    ·
      refine ⟨17646930438650820625062775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23529240584867760833417033 17646930438650820625062775)
      ·
        refine ⟨26470395657976230937594163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17646930438650820625062775 26470395657976230937594163)
        ·
          refine ⟨39705593486964346406391245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26470395657976230937594163 39705593486964346406391245)
          ·
            refine ⟨14889597557611629902396717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39705593486964346406391245 14889597557611629902396717)
            ·
              refine ⟨5583599084104361213398769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14889597557611629902396717 5583599084104361213398769)
              ·
                refine ⟨4187699313078270910049077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5583599084104361213398769 4187699313078270910049077)
                ·
                  refine ⟨392596810601087897817101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4187699313078270910049077 392596810601087897817101)
                  ·
                    rfl

theorem cell20_860152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 2, 5].length) (baseStart_860152 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_860152 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_860152 prefixEnd_860152 := by exact prefixLift 860152
  have htrace : WordTrace (prefixWord ++ tailWord_860152) baseStart_860152 baseEnd_860152 := by
    simpa [prefixWord, tailWord_860152, baseEnd_860152] using wordTrace_append hprefix tailTrace_860152
  have hstable : (prefixWord ++ tailWord_860152).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_860152).length < 2 ^ (prefixWord ++ tailWord_860152).sum := by decide
  have hdescent : baseEnd_860152 < baseStart_860152 := by decide
  rcases family_descends (prefixWord ++ tailWord_860152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_860155 : List Nat := [1, 1, 1, 1, 1, 3, 7, 3, 2]
def baseStart_860155 : Nat := 118140960795 + 860155 * 2 ^ 59
def prefixEnd_860155 : Nat := 4983230072969 + 3 ^ 40 * 860155 * 2
def baseEnd_860155 : Nat := 392598179882833220717089

theorem tailTrace_860155 : CollatzResearch.WordTrace tailWord_860155 prefixEnd_860155 392598179882833220717089 := by
  unfold tailWord_860155
  simp only [CollatzResearch.WordTrace]
  refine ⟨31372430198812812623581919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20914953465875208415721279 31372430198812812623581919)
  ·
    refine ⟨47058645298219218935372879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31372430198812812623581919 47058645298219218935372879)
    ·
      refine ⟨70587967947328828403059319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47058645298219218935372879 70587967947328828403059319)
      ·
        refine ⟨105881951920993242604588979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70587967947328828403059319 105881951920993242604588979)
        ·
          refine ⟨158822927881489863906883469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105881951920993242604588979 158822927881489863906883469)
          ·
            refine ⟨59558597955558698965081301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 158822927881489863906883469 59558597955558698965081301)
            ·
              refine ⟨1395904639583407006994093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 59558597955558698965081301 1395904639583407006994093)
              ·
                refine ⟨523464239843777627622785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1395904639583407006994093 523464239843777627622785)
                ·
                  refine ⟨392598179882833220717089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 523464239843777627622785 392598179882833220717089)
                  ·
                    rfl

theorem cell20_860155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 7, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 7, 3, 2].length) (baseStart_860155 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_860155 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_860155 prefixEnd_860155 := by exact prefixLift 860155
  have htrace : WordTrace (prefixWord ++ tailWord_860155) baseStart_860155 baseEnd_860155 := by
    simpa [prefixWord, tailWord_860155, baseEnd_860155] using wordTrace_append hprefix tailTrace_860155
  have hstable : (prefixWord ++ tailWord_860155).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_860155).length < 2 ^ (prefixWord ++ tailWord_860155).sum := by decide
  have hdescent : baseEnd_860155 < baseStart_860155 := by decide
  rcases family_descends (prefixWord ++ tailWord_860155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_860159 : List Nat := [1, 1, 2, 2, 1, 2, 1, 4, 6]
def baseStart_860159 : Nat := 118140960795 + 860159 * 2 ^ 59
def prefixEnd_860159 : Nat := 4983230072969 + 3 ^ 40 * 860159 * 2
def baseEnd_860159 : Nat := 392600005591826984583739

theorem tailTrace_860159 : CollatzResearch.WordTrace tailWord_860159 prefixEnd_860159 392600005591826984583739 := by
  unfold tailWord_860159
  simp only [CollatzResearch.WordTrace]
  refine ⟨31372576090798321306727531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20915050727198880871151687 31372576090798321306727531)
  ·
    refine ⟨47058864136197481960091297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31372576090798321306727531 47058864136197481960091297)
    ·
      refine ⟨35294148102148111470068473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47058864136197481960091297 35294148102148111470068473)
      ·
        refine ⟨26470611076611083602551355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35294148102148111470068473 26470611076611083602551355)
        ·
          refine ⟨39705916614916625403827033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26470611076611083602551355 39705916614916625403827033)
          ·
            refine ⟨29779437461187469052870275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39705916614916625403827033 29779437461187469052870275)
            ·
              refine ⟨44669156191781203579305413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29779437461187469052870275 44669156191781203579305413)
              ·
                refine ⟨8375466785958975671119765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44669156191781203579305413 8375466785958975671119765)
                ·
                  refine ⟨392600005591826984583739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8375466785958975671119765 392600005591826984583739)
                  ·
                    rfl

theorem cell20_860159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 4, 6].length) (baseStart_860159 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_860159 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_860159 prefixEnd_860159 := by exact prefixLift 860159
  have htrace : WordTrace (prefixWord ++ tailWord_860159) baseStart_860159 baseEnd_860159 := by
    simpa [prefixWord, tailWord_860159, baseEnd_860159] using wordTrace_append hprefix tailTrace_860159
  have hstable : (prefixWord ++ tailWord_860159).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_860159).length < 2 ^ (prefixWord ++ tailWord_860159).sum := by decide
  have hdescent : baseEnd_860159 < baseStart_860159 := by decide
  rcases family_descends (prefixWord ++ tailWord_860159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_860172 : List Nat := [2, 2, 1, 2, 3, 1, 5, 2, 2]
def baseStart_860172 : Nat := 118140960795 + 860172 * 2 ^ 59
def prefixEnd_860172 : Nat := 4983230072969 + 3 ^ 40 * 860172 * 2
def baseEnd_860172 : Nat := 392605939146056717150353

theorem tailTrace_860172 : CollatzResearch.WordTrace tailWord_860172 prefixEnd_860172 392605939146056717150353 := by
  unfold tailWord_860172
  simp only [CollatzResearch.WordTrace]
  refine ⟨15686525119875612263475385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20915366826500816351300513 15686525119875612263475385)
  ·
    refine ⟨11764893839906709197606539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15686525119875612263475385 11764893839906709197606539)
    ·
      refine ⟨17647340759860063796409809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11764893839906709197606539 17647340759860063796409809)
      ·
        refine ⟨13235505569895047847307357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17647340759860063796409809 13235505569895047847307357)
        ·
          refine ⟨4963314588710642942740259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13235505569895047847307357 4963314588710642942740259)
          ·
            refine ⟨7444971883065964414110389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4963314588710642942740259 7444971883065964414110389)
            ·
              refine ⟨697966114037434163822849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7444971883065964414110389 697966114037434163822849)
              ·
                refine ⟨523474585528075622867137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 697966114037434163822849 523474585528075622867137)
                ·
                  refine ⟨392605939146056717150353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 523474585528075622867137 392605939146056717150353)
                  ·
                    rfl

theorem cell20_860172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 5, 2, 2].length) (baseStart_860172 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_860172 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_860172 prefixEnd_860172 := by exact prefixLift 860172
  have htrace : WordTrace (prefixWord ++ tailWord_860172) baseStart_860172 baseEnd_860172 := by
    simpa [prefixWord, tailWord_860172, baseEnd_860172] using wordTrace_append hprefix tailTrace_860172
  have hstable : (prefixWord ++ tailWord_860172).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_860172).length < 2 ^ (prefixWord ++ tailWord_860172).sum := by decide
  have hdescent : baseEnd_860172 < baseStart_860172 := by decide
  rcases family_descends (prefixWord ++ tailWord_860172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_860186 : List Nat := [3, 1, 1, 3, 1, 3, 4, 1, 3]
def baseStart_860186 : Nat := 118140960795 + 860186 * 2 ^ 59
def prefixEnd_860186 : Nat := 4983230072969 + 3 ^ 40 * 860186 * 2
def baseEnd_860186 : Nat := 392612329127534890683629

theorem tailTrace_860186 : CollatzResearch.WordTrace tailWord_860186 prefixEnd_860186 392612329127534890683629 := by
  unfold tailWord_860186
  simp only [CollatzResearch.WordTrace]
  refine ⟨7843390215425126229490103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20915707241133669945306941 7843390215425126229490103)
  ·
    refine ⟨11765085323137689344235155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7843390215425126229490103 11765085323137689344235155)
    ·
      refine ⟨17647627984706534016352733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11765085323137689344235155 17647627984706534016352733)
      ·
        refine ⟨6617860494264950256132275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17647627984706534016352733 6617860494264950256132275)
        ·
          refine ⟨9926790741397425384198413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6617860494264950256132275 9926790741397425384198413)
          ·
            refine ⟨3722546528024034519074405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9926790741397425384198413 3722546528024034519074405)
            ·
              refine ⟨697977474004506472326451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3722546528024034519074405 697977474004506472326451)
              ·
                refine ⟨1046966211006759708489677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 697977474004506472326451 1046966211006759708489677)
                ·
                  refine ⟨392612329127534890683629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1046966211006759708489677 392612329127534890683629)
                  ·
                    rfl

theorem cell20_860186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 4, 1, 3].length) (baseStart_860186 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_860186 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_860186 prefixEnd_860186 := by exact prefixLift 860186
  have htrace : WordTrace (prefixWord ++ tailWord_860186) baseStart_860186 baseEnd_860186 := by
    simpa [prefixWord, tailWord_860186, baseEnd_860186] using wordTrace_append hprefix tailTrace_860186
  have hstable : (prefixWord ++ tailWord_860186).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_860186).length < 2 ^ (prefixWord ++ tailWord_860186).sum := by decide
  have hdescent : baseEnd_860186 < baseStart_860186 := by decide
  rcases family_descends (prefixWord ++ tailWord_860186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_860231 : List Nat := [1, 1, 4, 1, 3, 1, 3, 4, 2]
def baseStart_860231 : Nat := 118140960795 + 860231 * 2 ^ 59
def prefixEnd_860231 : Nat := 4983230072969 + 3 ^ 40 * 860231 * 2
def baseEnd_860231 : Nat := 392632868353714734183445

theorem tailTrace_860231 : CollatzResearch.WordTrace tailWord_860231 prefixEnd_860231 392632868353714734183445 := by
  unfold tailWord_860231
  simp only [CollatzResearch.WordTrace]
  refine ⟨31375202146537477603348547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20916801431024985068899031 31375202146537477603348547)
  ·
    refine ⟨47062803219806216405022821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31375202146537477603348547 47062803219806216405022821)
    ·
      refine ⟨8824275603713665575941779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47062803219806216405022821 8824275603713665575941779)
      ·
        refine ⟨13236413405570498363912669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8824275603713665575941779 13236413405570498363912669)
        ·
          refine ⟨4963655027088936886467251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13236413405570498363912669 4963655027088936886467251)
          ·
            refine ⟨7445482540633405329700877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4963655027088936886467251 7445482540633405329700877)
            ·
              refine ⟨2792055952737526998637829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7445482540633405329700877 2792055952737526998637829)
              ·
                refine ⟨523510491138286312244593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2792055952737526998637829 523510491138286312244593)
                ·
                  refine ⟨392632868353714734183445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 523510491138286312244593 392632868353714734183445)
                  ·
                    rfl

theorem cell20_860231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 3, 4, 2].length) (baseStart_860231 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_860231 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_860231 prefixEnd_860231 := by exact prefixLift 860231
  have htrace : WordTrace (prefixWord ++ tailWord_860231) baseStart_860231 baseEnd_860231 := by
    simpa [prefixWord, tailWord_860231, baseEnd_860231] using wordTrace_append hprefix tailTrace_860231
  have hstable : (prefixWord ++ tailWord_860231).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_860231).length < 2 ^ (prefixWord ++ tailWord_860231).sum := by decide
  have hdescent : baseEnd_860231 < baseStart_860231 := by decide
  rcases family_descends (prefixWord ++ tailWord_860231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_860238 : List Nat := [4, 1, 1, 1, 1, 6, 1, 5]
def baseStart_860238 : Nat := 118140960795 + 860238 * 2 ^ 59
def prefixEnd_860238 : Nat := 4983230072969 + 3 ^ 40 * 860238 * 2
def baseEnd_860238 : Nat := 130878687781484606983361

theorem tailTrace_860238 : CollatzResearch.WordTrace tailWord_860238 prefixEnd_860238 130878687781484606983361 := by
  unfold tailWord_860238
  simp only [CollatzResearch.WordTrace]
  refine ⟨3921932182189014724856671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20916971638341411865902245 3921932182189014724856671)
  ·
    refine ⟨5882898273283522087285007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3921932182189014724856671 5882898273283522087285007)
    ·
      refine ⟨8824347409925283130927511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5882898273283522087285007 8824347409925283130927511)
      ·
        refine ⟨13236521114887924696391267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8824347409925283130927511 13236521114887924696391267)
        ·
          refine ⟨19854781672331887044586901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13236521114887924696391267 19854781672331887044586901)
          ·
            refine ⟨930692890890557205215011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 19854781672331887044586901 930692890890557205215011)
            ·
              refine ⟨1396039336335835807822517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 930692890890557205215011 1396039336335835807822517)
              ·
                refine ⟨130878687781484606983361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1396039336335835807822517 130878687781484606983361)
                ·
                  rfl

theorem cell20_860238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 1, 5].length) (baseStart_860238 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_860238 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_860238 prefixEnd_860238 := by exact prefixLift 860238
  have htrace : WordTrace (prefixWord ++ tailWord_860238) baseStart_860238 baseEnd_860238 := by
    simpa [prefixWord, tailWord_860238, baseEnd_860238] using wordTrace_append hprefix tailTrace_860238
  have hstable : (prefixWord ++ tailWord_860238).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_860238).length < 2 ^ (prefixWord ++ tailWord_860238).sum := by decide
  have hdescent : baseEnd_860238 < baseStart_860238 := by decide
  rcases family_descends (prefixWord ++ tailWord_860238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_860245 : List Nat := [1, 3, 2, 2, 1, 3, 2, 3, 3]
def baseStart_860245 : Nat := 118140960795 + 860245 * 2 ^ 59
def prefixEnd_860245 : Nat := 4983230072969 + 3 ^ 40 * 860245 * 2
def baseEnd_860245 : Nat := 392639258335192907716721

theorem tailTrace_860245 : CollatzResearch.WordTrace tailWord_860245 prefixEnd_860245 392639258335192907716721 := by
  unfold tailWord_860245
  simp only [CollatzResearch.WordTrace]
  refine ⟨31375712768486757994358189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20917141845657838662905459 31375712768486757994358189)
  ·
    refine ⟨11765892288182534247884321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31375712768486757994358189 11765892288182534247884321)
    ·
      refine ⟨8824419216136900685913241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11765892288182534247884321 8824419216136900685913241)
      ·
        refine ⟨6618314412102675514434931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8824419216136900685913241 6618314412102675514434931)
        ·
          refine ⟨9927471618154013271652397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6618314412102675514434931 9927471618154013271652397)
          ·
            refine ⟨3722801856807754976869649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9927471618154013271652397 3722801856807754976869649)
            ·
              refine ⟨2792101392605816232652237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3722801856807754976869649 2792101392605816232652237)
              ·
                refine ⟨1047038022227181087244589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2792101392605816232652237 1047038022227181087244589)
                ·
                  refine ⟨392639258335192907716721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1047038022227181087244589 392639258335192907716721)
                  ·
                    rfl

theorem cell20_860245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 2, 3, 3].length) (baseStart_860245 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_860245 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_860245 prefixEnd_860245 := by exact prefixLift 860245
  have htrace : WordTrace (prefixWord ++ tailWord_860245) baseStart_860245 baseEnd_860245 := by
    simpa [prefixWord, tailWord_860245, baseEnd_860245] using wordTrace_append hprefix tailTrace_860245
  have hstable : (prefixWord ++ tailWord_860245).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_860245).length < 2 ^ (prefixWord ++ tailWord_860245).sum := by decide
  have hdescent : baseEnd_860245 < baseStart_860245 := by decide
  rcases family_descends (prefixWord ++ tailWord_860245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_860252 : List Nat := [2, 2, 4, 1, 1, 2, 1, 1, 6]
def baseStart_860252 : Nat := 118140960795 + 860252 * 2 ^ 59
def prefixEnd_860252 : Nat := 4983230072969 + 3 ^ 40 * 860252 * 2
def baseEnd_860252 : Nat := 392642453325931994483359

theorem tailTrace_860252 : CollatzResearch.WordTrace tailWord_860252 prefixEnd_860252 392642453325931994483359 := by
  unfold tailWord_860252
  simp only [CollatzResearch.WordTrace]
  refine ⟨15687984039730699094931505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20917312052974265459908673 15687984039730699094931505)
  ·
    refine ⟨11765988029798024321198629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15687984039730699094931505 11765988029798024321198629)
    ·
      refine ⟨2206122755587129560224743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11765988029798024321198629 2206122755587129560224743)
      ·
        refine ⟨3309184133380694340337115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2206122755587129560224743 3309184133380694340337115)
        ·
          refine ⟨4963776200071041510505673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3309184133380694340337115 4963776200071041510505673)
          ·
            refine ⟨3722832150053281132879255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4963776200071041510505673 3722832150053281132879255)
            ·
              refine ⟨5584248225079921699318883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3722832150053281132879255 5584248225079921699318883)
              ·
                refine ⟨8376372337619882548978325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5584248225079921699318883 8376372337619882548978325)
                ·
                  refine ⟨392642453325931994483359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8376372337619882548978325 392642453325931994483359)
                  ·
                    rfl

theorem cell20_860252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 1, 6].length) (baseStart_860252 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_860252 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_860252 prefixEnd_860252 := by exact prefixLift 860252
  have htrace : WordTrace (prefixWord ++ tailWord_860252) baseStart_860252 baseEnd_860252 := by
    simpa [prefixWord, tailWord_860252, baseEnd_860252] using wordTrace_append hprefix tailTrace_860252
  have hstable : (prefixWord ++ tailWord_860252).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_860252).length < 2 ^ (prefixWord ++ tailWord_860252).sum := by decide
  have hdescent : baseEnd_860252 < baseStart_860252 := by decide
  rcases family_descends (prefixWord ++ tailWord_860252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_860273 : List Nat := [1, 2, 2, 2, 1, 1, 3, 2, 6]
def baseStart_860273 : Nat := 118140960795 + 860273 * 2 ^ 59
def prefixEnd_860273 : Nat := 4983230072969 + 3 ^ 40 * 860273 * 2
def baseEnd_860273 : Nat := 392652038298149254783273

theorem tailTrace_860273 : CollatzResearch.WordTrace tailWord_860273 prefixEnd_860273 392652038298149254783273 := by
  unfold tailWord_860273
  simp only [CollatzResearch.WordTrace]
  refine ⟨31376734012385318776377473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20917822674923545850918315 31376734012385318776377473)
  ·
    refine ⟨23532550509288989082283105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31376734012385318776377473 23532550509288989082283105)
    ·
      refine ⟨17649412881966741811712329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23532550509288989082283105 17649412881966741811712329)
      ·
        refine ⟨13237059661475056358784247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17649412881966741811712329 13237059661475056358784247)
        ·
          refine ⟨19855589492212584538176371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13237059661475056358784247 19855589492212584538176371)
          ·
            refine ⟨29783384238318876807264557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19855589492212584538176371 29783384238318876807264557)
            ·
              refine ⟨11168769089369578802724209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29783384238318876807264557 11168769089369578802724209)
              ·
                refine ⟨8376576817027184102043157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11168769089369578802724209 8376576817027184102043157)
                ·
                  refine ⟨392652038298149254783273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8376576817027184102043157 392652038298149254783273)
                  ·
                    rfl

theorem cell20_860273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 2, 6].length) (baseStart_860273 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_860273 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_860273 prefixEnd_860273 := by exact prefixLift 860273
  have htrace : WordTrace (prefixWord ++ tailWord_860273) baseStart_860273 baseEnd_860273 := by
    simpa [prefixWord, tailWord_860273, baseEnd_860273] using wordTrace_append hprefix tailTrace_860273
  have hstable : (prefixWord ++ tailWord_860273).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_860273).length < 2 ^ (prefixWord ++ tailWord_860273).sum := by decide
  have hdescent : baseEnd_860273 < baseStart_860273 := by decide
  rcases family_descends (prefixWord ++ tailWord_860273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_860314 : List Nat := [3, 1, 1, 5, 2, 1, 1, 6]
def baseStart_860314 : Nat := 118140960795 + 860314 * 2 ^ 59
def prefixEnd_860314 : Nat := 4983230072969 + 3 ^ 40 * 860314 * 2
def baseEnd_860314 : Nat := 130890250605111778138813

theorem tailTrace_860314 : CollatzResearch.WordTrace tailWord_860314 prefixEnd_860314 130890250605111778138813 := by
  unfold tailWord_860314
  simp only [CollatzResearch.WordTrace]
  refine ⟨7844557351309195694654999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20918819603491188519079997 7844557351309195694654999)
  ·
    refine ⟨11766836026963793541982499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7844557351309195694654999 11766836026963793541982499)
    ·
      refine ⟨17650254040445690312973749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11766836026963793541982499 17650254040445690312973749)
      ·
        refine ⟨1654711316291783466841289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 17650254040445690312973749 1654711316291783466841289)
        ·
          refine ⟨1241033487218837600130967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1654711316291783466841289 1241033487218837600130967)
          ·
            refine ⟨1861550230828256400196451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1241033487218837600130967 1861550230828256400196451)
            ·
              refine ⟨2792325346242384600294677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1861550230828256400196451 2792325346242384600294677)
              ·
                refine ⟨130890250605111778138813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2792325346242384600294677 130890250605111778138813)
                ·
                  rfl

theorem cell20_860314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 1, 6].length) (baseStart_860314 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_860314 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_860314 prefixEnd_860314 := by exact prefixLift 860314
  have htrace : WordTrace (prefixWord ++ tailWord_860314) baseStart_860314 baseEnd_860314 := by
    simpa [prefixWord, tailWord_860314, baseEnd_860314] using wordTrace_append hprefix tailTrace_860314
  have hstable : (prefixWord ++ tailWord_860314).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_860314).length < 2 ^ (prefixWord ++ tailWord_860314).sum := by decide
  have hdescent : baseEnd_860314 < baseStart_860314 := by decide
  rcases family_descends (prefixWord ++ tailWord_860314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_860341 : List Nat := [1, 3, 3, 4, 2, 1, 1, 1, 4]
def baseStart_860341 : Nat := 118140960795 + 860341 * 2 ^ 59
def prefixEnd_860341 : Nat := 4983230072969 + 3 ^ 40 * 860341 * 2
def baseEnd_860341 : Nat := 392683075351043240516329

theorem tailTrace_860341 : CollatzResearch.WordTrace tailWord_860341 prefixEnd_860341 392683075351043240516329 := by
  unfold tailWord_860341
  simp only [CollatzResearch.WordTrace]
  refine ⟨31379214176138966389852877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20919476117425977593235251 31379214176138966389852877)
  ·
    refine ⟨11767205316052112396194829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31379214176138966389852877 11767205316052112396194829)
    ·
      refine ⟨4412701993519542148573061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11767205316052112396194829 4412701993519542148573061)
      ·
        refine ⟨827381623784914152857449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4412701993519542148573061 827381623784914152857449)
        ·
          refine ⟨620536217838685614643087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 827381623784914152857449 620536217838685614643087)
          ·
            refine ⟨930804326758028421964631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 620536217838685614643087 930804326758028421964631)
            ·
              refine ⟨1396206490137042632946947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 930804326758028421964631 1396206490137042632946947)
              ·
                refine ⟨2094309735205563949420421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1396206490137042632946947 2094309735205563949420421)
                ·
                  refine ⟨392683075351043240516329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2094309735205563949420421 392683075351043240516329)
                  ·
                    rfl

theorem cell20_860341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 1, 1, 4].length) (baseStart_860341 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_860341 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_860341 prefixEnd_860341 := by exact prefixLift 860341
  have htrace : WordTrace (prefixWord ++ tailWord_860341) baseStart_860341 baseEnd_860341 := by
    simpa [prefixWord, tailWord_860341, baseEnd_860341] using wordTrace_append hprefix tailTrace_860341
  have hstable : (prefixWord ++ tailWord_860341).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_860341).length < 2 ^ (prefixWord ++ tailWord_860341).sum := by decide
  have hdescent : baseEnd_860341 < baseStart_860341 := by decide
  rcases family_descends (prefixWord ++ tailWord_860341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_860386 : List Nat := [3, 3, 4, 1, 2, 7]
def baseStart_860386 : Nat := 118140960795 + 860386 * 2 ^ 59
def prefixEnd_860386 : Nat := 4983230072969 + 3 ^ 40 * 860386 * 2
def baseEnd_860386 : Nat := 14544578317674929037635

theorem tailTrace_860386 : CollatzResearch.WordTrace tailWord_860386 prefixEnd_860386 14544578317674929037635 := by
  unfold tailWord_860386
  simp only [CollatzResearch.WordTrace]
  refine ⟨7845213865243984768810253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20920570307317292716827341 7845213865243984768810253)
  ·
    refine ⟨2941955199466494288303845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7845213865243984768810253 2941955199466494288303845)
    ·
      refine ⟨551616599899967679056971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2941955199466494288303845 551616599899967679056971)
      ·
        refine ⟨827424899849951518585457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 551616599899967679056971 827424899849951518585457)
        ·
          refine ⟨620568674887463638939093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 827424899849951518585457 620568674887463638939093)
          ·
            refine ⟨14544578317674929037635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 620568674887463638939093 14544578317674929037635)
            ·
              rfl

theorem cell20_860386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 7].length) (baseStart_860386 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_860386 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_860386 prefixEnd_860386 := by exact prefixLift 860386
  have htrace : WordTrace (prefixWord ++ tailWord_860386) baseStart_860386 baseEnd_860386 := by
    simpa [prefixWord, tailWord_860386, baseEnd_860386] using wordTrace_append hprefix tailTrace_860386
  have hstable : (prefixWord ++ tailWord_860386).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_860386).length < 2 ^ (prefixWord ++ tailWord_860386).sum := by decide
  have hdescent : baseEnd_860386 < baseStart_860386 := by decide
  rcases family_descends (prefixWord ++ tailWord_860386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_860425 : List Nat := [1, 2, 1, 1, 3, 4, 1, 1, 6]
def baseStart_860425 : Nat := 118140960795 + 860425 * 2 ^ 59
def prefixEnd_860425 : Nat := 4983230072969 + 3 ^ 40 * 860425 * 2
def baseEnd_860425 : Nat := 392721415239912281715985

theorem tailTrace_860425 : CollatzResearch.WordTrace tailWord_860425 prefixEnd_860425 392721415239912281715985 := by
  unfold tailWord_860425
  simp only [CollatzResearch.WordTrace]
  refine ⟨31382277907834648735910729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20921518605223099157273819 31382277907834648735910729)
  ·
    refine ⟨23536708430875986551933047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31382277907834648735910729 23536708430875986551933047)
    ·
      refine ⟨35305062646313979827899571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23536708430875986551933047 35305062646313979827899571)
      ·
        refine ⟨52957593969470969741849357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35305062646313979827899571 52957593969470969741849357)
        ·
          refine ⟨19859097738551613653193509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52957593969470969741849357 19859097738551613653193509)
          ·
            refine ⟨3723580825978427559973783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19859097738551613653193509 3723580825978427559973783)
            ·
              refine ⟨5585371238967641339960675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3723580825978427559973783 5585371238967641339960675)
              ·
                refine ⟨8378056858451462009941013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5585371238967641339960675 8378056858451462009941013)
                ·
                  refine ⟨392721415239912281715985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8378056858451462009941013 392721415239912281715985)
                  ·
                    rfl

theorem cell20_860425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 1, 6].length) (baseStart_860425 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_860425 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_860425 prefixEnd_860425 := by exact prefixLift 860425
  have htrace : WordTrace (prefixWord ++ tailWord_860425) baseStart_860425 baseEnd_860425 := by
    simpa [prefixWord, tailWord_860425, baseEnd_860425] using wordTrace_append hprefix tailTrace_860425
  have hstable : (prefixWord ++ tailWord_860425).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_860425).length < 2 ^ (prefixWord ++ tailWord_860425).sum := by decide
  have hdescent : baseEnd_860425 < baseStart_860425 := by decide
  rcases family_descends (prefixWord ++ tailWord_860425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_860452 : List Nat := [2, 3, 1, 3, 1, 4, 1, 2, 3]
def baseStart_860452 : Nat := 118140960795 + 860452 * 2 ^ 59
def prefixEnd_860452 : Nat := 4983230072969 + 3 ^ 40 * 860452 * 2
def baseEnd_860452 : Nat := 392733738775620187815875

theorem tailTrace_860452 : CollatzResearch.WordTrace tailWord_860452 prefixEnd_860452 392733738775620187815875 := by
  unfold tailWord_860452
  simp only [CollatzResearch.WordTrace]
  refine ⟨15691631339368416173571805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20922175119157888231429073 15691631339368416173571805)
  ·
    refine ⟨5884361752263156065089427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15691631339368416173571805 5884361752263156065089427)
    ·
      refine ⟨8826542628394734097634141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5884361752263156065089427 8826542628394734097634141)
      ·
        refine ⟨3309953485648025286612803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8826542628394734097634141 3309953485648025286612803)
        ·
          refine ⟨4964930228472037929919205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3309953485648025286612803 4964930228472037929919205)
          ·
            refine ⟨930924417838507111859851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4964930228472037929919205 930924417838507111859851)
            ·
              refine ⟨1396386626757760667789777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 930924417838507111859851 1396386626757760667789777)
              ·
                refine ⟨1047289970068320500842333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1396386626757760667789777 1047289970068320500842333)
                ·
                  refine ⟨392733738775620187815875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1047289970068320500842333 392733738775620187815875)
                  ·
                    rfl

theorem cell20_860452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 1, 2, 3].length) (baseStart_860452 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_860452 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_860452 prefixEnd_860452 := by exact prefixLift 860452
  have htrace : WordTrace (prefixWord ++ tailWord_860452) baseStart_860452 baseEnd_860452 := by
    simpa [prefixWord, tailWord_860452, baseEnd_860452] using wordTrace_append hprefix tailTrace_860452
  have hstable : (prefixWord ++ tailWord_860452).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_860452).length < 2 ^ (prefixWord ++ tailWord_860452).sum := by decide
  have hdescent : baseEnd_860452 < baseStart_860452 := by decide
  rcases family_descends (prefixWord ++ tailWord_860452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_860455 : List Nat := [1, 1, 8, 1, 1, 1, 2, 1, 4]
def baseStart_860455 : Nat := 118140960795 + 860455 * 2 ^ 59
def prefixEnd_860455 : Nat := 4983230072969 + 3 ^ 40 * 860455 * 2
def baseEnd_860455 : Nat := 392735108057365510715863

theorem tailTrace_860455 : CollatzResearch.WordTrace tailWord_860455 prefixEnd_860455 392735108057365510715863 := by
  unfold tailWord_860455
  simp only [CollatzResearch.WordTrace]
  refine ⟨31383372097725963859502819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20922248065150642573001879 31383372097725963859502819)
  ·
    refine ⟨47075058146588945789254229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31383372097725963859502819 47075058146588945789254229)
    ·
      refine ⟨551660837655339208467823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 47075058146588945789254229 551660837655339208467823)
      ·
        refine ⟨827491256483008812701735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 551660837655339208467823 827491256483008812701735)
        ·
          refine ⟨1241236884724513219052603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 827491256483008812701735 1241236884724513219052603)
          ·
            refine ⟨1861855327086769828578905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1241236884724513219052603 1861855327086769828578905)
            ·
              refine ⟨1396391495315077371434179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1861855327086769828578905 1396391495315077371434179)
              ·
                refine ⟨2094587242972616057151269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1396391495315077371434179 2094587242972616057151269)
                ·
                  refine ⟨392735108057365510715863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2094587242972616057151269 392735108057365510715863)
                  ·
                    rfl

theorem cell20_860455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 2, 1, 4].length) (baseStart_860455 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_860455 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_860455 prefixEnd_860455 := by exact prefixLift 860455
  have htrace : WordTrace (prefixWord ++ tailWord_860455) baseStart_860455 baseEnd_860455 := by
    simpa [prefixWord, tailWord_860455, baseEnd_860455] using wordTrace_append hprefix tailTrace_860455
  have hstable : (prefixWord ++ tailWord_860455).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_860455).length < 2 ^ (prefixWord ++ tailWord_860455).sum := by decide
  have hdescent : baseEnd_860455 < baseStart_860455 := by decide
  rcases family_descends (prefixWord ++ tailWord_860455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_860463 : List Nat := [1, 1, 2, 1, 2, 1, 5, 3, 4]
def baseStart_860463 : Nat := 118140960795 + 860463 * 2 ^ 59
def prefixEnd_860463 : Nat := 4983230072969 + 3 ^ 40 * 860463 * 2
def baseEnd_860463 : Nat := 392738759475353038449163

theorem tailTrace_860463 : CollatzResearch.WordTrace tailWord_860463 prefixEnd_860463 392738759475353038449163 := by
  unfold tailWord_860463
  simp only [CollatzResearch.WordTrace]
  refine ⟨31383663881696981225794043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20922442587797987483862695 31383663881696981225794043)
  ·
    refine ⟨47075495822545471838691065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31383663881696981225794043 47075495822545471838691065)
    ·
      refine ⟨35306621866909103879018299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47075495822545471838691065 35306621866909103879018299)
      ·
        refine ⟨52959932800363655818527449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35306621866909103879018299 52959932800363655818527449)
        ·
          refine ⟨39719949600272741863895587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52959932800363655818527449 39719949600272741863895587)
          ·
            refine ⟨59579924400409112795843381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39719949600272741863895587 59579924400409112795843381)
            ·
              refine ⟨5585617912538354324610317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 59579924400409112795843381 5585617912538354324610317)
              ·
                refine ⟨2094606717201882871728869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5585617912538354324610317 2094606717201882871728869)
                ·
                  refine ⟨392738759475353038449163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2094606717201882871728869 392738759475353038449163)
                  ·
                    rfl

theorem cell20_860463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 3, 4].length) (baseStart_860463 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_860463 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_860463 prefixEnd_860463 := by exact prefixLift 860463
  have htrace : WordTrace (prefixWord ++ tailWord_860463) baseStart_860463 baseEnd_860463 := by
    simpa [prefixWord, tailWord_860463, baseEnd_860463] using wordTrace_append hprefix tailTrace_860463
  have hstable : (prefixWord ++ tailWord_860463).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_860463).length < 2 ^ (prefixWord ++ tailWord_860463).sum := by decide
  have hdescent : baseEnd_860463 < baseStart_860463 := by decide
  rcases family_descends (prefixWord ++ tailWord_860463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_860497 : List Nat := [1, 2, 2, 1, 4, 2, 3, 3, 2]
def baseStart_860497 : Nat := 118140960795 + 860497 * 2 ^ 59
def prefixEnd_860497 : Nat := 4983230072969 + 3 ^ 40 * 860497 * 2
def baseEnd_860497 : Nat := 392754278001800031315691

theorem tailTrace_860497 : CollatzResearch.WordTrace tailWord_860497 prefixEnd_860497 392754278001800031315691 := by
  unfold tailWord_860497
  simp only [CollatzResearch.WordTrace]
  refine ⟨31384903963573805032531745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20923269309049203355021163 31384903963573805032531745)
  ·
    refine ⟨23538677972680353774398809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31384903963573805032531745 23538677972680353774398809)
    ·
      refine ⟨17654008479510265330799107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23538677972680353774398809 17654008479510265330799107)
      ·
        refine ⟨26481012719265397996198661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17654008479510265330799107 26481012719265397996198661)
        ·
          refine ⟨4965189884862262124287249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26481012719265397996198661 4965189884862262124287249)
          ·
            refine ⟨3723892413646696593215437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4965189884862262124287249 3723892413646696593215437)
            ·
              refine ⟨1396459655117511222455789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3723892413646696593215437 1396459655117511222455789)
              ·
                refine ⟨523672370669066708420921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1396459655117511222455789 523672370669066708420921)
                ·
                  refine ⟨392754278001800031315691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 523672370669066708420921 392754278001800031315691)
                  ·
                    rfl

theorem cell20_860497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 3, 3, 2].length) (baseStart_860497 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_860497 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_860497 prefixEnd_860497 := by exact prefixLift 860497
  have htrace : WordTrace (prefixWord ++ tailWord_860497) baseStart_860497 baseEnd_860497 := by
    simpa [prefixWord, tailWord_860497, baseEnd_860497] using wordTrace_append hprefix tailTrace_860497
  have hstable : (prefixWord ++ tailWord_860497).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_860497).length < 2 ^ (prefixWord ++ tailWord_860497).sum := by decide
  have hdescent : baseEnd_860497 < baseStart_860497 := by decide
  rcases family_descends (prefixWord ++ tailWord_860497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_860525 : List Nat := [1, 5, 1, 1, 1, 2, 4, 5]
def baseStart_860525 : Nat := 118140960795 + 860525 * 2 ^ 59
def prefixEnd_860525 : Nat := 4983230072969 + 3 ^ 40 * 860525 * 2
def baseEnd_860525 : Nat := 130922352654918792794081

theorem tailTrace_860525 : CollatzResearch.WordTrace tailWord_860525 prefixEnd_860525 130922352654918792794081 := by
  unfold tailWord_860525
  simp only [CollatzResearch.WordTrace]
  refine ⟨31385925207472365814551029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20923950138314910543034019 31385925207472365814551029)
  ·
    refine ⟨2942430488200534295114159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 31385925207472365814551029 2942430488200534295114159)
    ·
      refine ⟨4413645732300801442671239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2942430488200534295114159 4413645732300801442671239)
      ·
        refine ⟨6620468598451202164006859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4413645732300801442671239 6620468598451202164006859)
        ·
          refine ⟨9930702897676803246010289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6620468598451202164006859 9930702897676803246010289)
          ·
            refine ⟨7448027173257602434507717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9930702897676803246010289 7448027173257602434507717)
            ·
              refine ⟨1396505094985800456470197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7448027173257602434507717 1396505094985800456470197)
              ·
                refine ⟨130922352654918792794081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1396505094985800456470197 130922352654918792794081)
                ·
                  rfl

theorem cell20_860525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 4, 5].length) (baseStart_860525 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_860525 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_860525 prefixEnd_860525 := by exact prefixLift 860525
  have htrace : WordTrace (prefixWord ++ tailWord_860525) baseStart_860525 baseEnd_860525 := by
    simpa [prefixWord, tailWord_860525, baseEnd_860525] using wordTrace_append hprefix tailTrace_860525
  have hstable : (prefixWord ++ tailWord_860525).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_860525).length < 2 ^ (prefixWord ++ tailWord_860525).sum := by decide
  have hdescent : baseEnd_860525 < baseStart_860525 := by decide
  rcases family_descends (prefixWord ++ tailWord_860525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_860528 : List Nat := [2, 1, 1, 1, 4, 5, 2, 1, 3]
def baseStart_860528 : Nat := 118140960795 + 860528 * 2 ^ 59
def prefixEnd_860528 : Nat := 4983230072969 + 3 ^ 40 * 860528 * 2
def baseEnd_860528 : Nat := 392768427246501701282231

theorem tailTrace_860528 : CollatzResearch.WordTrace tailWord_860528 prefixEnd_860528 392768427246501701282231 := by
  unfold tailWord_860528
  simp only [CollatzResearch.WordTrace]
  refine ⟨15693017313230748663455119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20924023084307664884606825 15693017313230748663455119)
  ·
    refine ⟨23539525969846122995182679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15693017313230748663455119 23539525969846122995182679)
    ·
      refine ⟨35309288954769184492774019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23539525969846122995182679 35309288954769184492774019)
      ·
        refine ⟨52963933432153776739161029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35309288954769184492774019 52963933432153776739161029)
        ·
          refine ⟨9930737518528833138592693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52963933432153776739161029 9930737518528833138592693)
          ·
            refine ⟨931006642362078106743065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9930737518528833138592693 931006642362078106743065)
            ·
              refine ⟨698254981771558580057299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 931006642362078106743065 698254981771558580057299)
              ·
                refine ⟨1047382472657337870085949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 698254981771558580057299 1047382472657337870085949)
                ·
                  refine ⟨392768427246501701282231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1047382472657337870085949 392768427246501701282231)
                  ·
                    rfl

theorem cell20_860528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 2, 1, 3].length) (baseStart_860528 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_860528 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_860528 prefixEnd_860528 := by exact prefixLift 860528
  have htrace : WordTrace (prefixWord ++ tailWord_860528) baseStart_860528 baseEnd_860528 := by
    simpa [prefixWord, tailWord_860528, baseEnd_860528] using wordTrace_append hprefix tailTrace_860528
  have hstable : (prefixWord ++ tailWord_860528).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_860528).length < 2 ^ (prefixWord ++ tailWord_860528).sum := by decide
  have hdescent : baseEnd_860528 < baseStart_860528 := by decide
  rcases family_descends (prefixWord ++ tailWord_860528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_860591 : List Nat := [1, 1, 2, 1, 2, 2, 1, 1, 9]
def baseStart_860591 : Nat := 118140960795 + 860591 * 2 ^ 59
def prefixEnd_860591 : Nat := 4983230072969 + 3 ^ 40 * 860591 * 2
def baseEnd_860591 : Nat := 392797182163153482181973

theorem tailTrace_860591 : CollatzResearch.WordTrace tailWord_860591 prefixEnd_860591 392797182163153482181973 := by
  unfold tailWord_860591
  simp only [CollatzResearch.WordTrace]
  refine ⟨31388332425233259086453627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20925554950155506057635751 31388332425233259086453627)
  ·
    refine ⟨47082498637849888629680441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31388332425233259086453627 47082498637849888629680441)
    ·
      refine ⟨35311873978387416472260331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47082498637849888629680441 35311873978387416472260331)
      ·
        refine ⟨52967810967581124708390497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35311873978387416472260331 52967810967581124708390497)
        ·
          refine ⟨39725858225685843531292873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52967810967581124708390497 39725858225685843531292873)
          ·
            refine ⟨29794393669264382648469655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39725858225685843531292873 29794393669264382648469655)
            ·
              refine ⟨44691590503896573972704483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29794393669264382648469655 44691590503896573972704483)
              ·
                refine ⟨67037385755844860959056725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44691590503896573972704483 67037385755844860959056725)
                ·
                  refine ⟨392797182163153482181973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 67037385755844860959056725 392797182163153482181973)
                  ·
                    rfl

theorem cell20_860591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 9].length) (baseStart_860591 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_860591 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_860591 prefixEnd_860591 := by exact prefixLift 860591
  have htrace : WordTrace (prefixWord ++ tailWord_860591) baseStart_860591 baseEnd_860591 := by
    simpa [prefixWord, tailWord_860591, baseEnd_860591] using wordTrace_append hprefix tailTrace_860591
  have hstable : (prefixWord ++ tailWord_860591).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_860591).length < 2 ^ (prefixWord ++ tailWord_860591).sum := by decide
  have hdescent : baseEnd_860591 < baseStart_860591 := by decide
  rcases family_descends (prefixWord ++ tailWord_860591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_860684 : List Nat := [2, 2, 1, 2, 4, 1, 2, 1, 5]
def baseStart_860684 : Nat := 118140960795 + 860684 * 2 ^ 59
def prefixEnd_860684 : Nat := 4983230072969 + 3 ^ 40 * 860684 * 2
def baseEnd_860684 : Nat := 392839629897258492081593

theorem tailTrace_860684 : CollatzResearch.WordTrace tailWord_860684 prefixEnd_860684 392839629897258492081593 := by
  unfold tailWord_860684
  simp only [CollatzResearch.WordTrace]
  refine ⟨15695862206948167984794553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20927816275930890646392737 15695862206948167984794553)
  ·
    refine ⟨11771896655211125988595915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15695862206948167984794553 11771896655211125988595915)
    ·
      refine ⟨17657844982816688982893873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11771896655211125988595915 17657844982816688982893873)
      ·
        refine ⟨13243383737112516737170405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17657844982816688982893873 13243383737112516737170405)
        ·
          refine ⟨2483134450708596888219451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13243383737112516737170405 2483134450708596888219451)
          ·
            refine ⟨3724701676062895332329177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2483134450708596888219451 3724701676062895332329177)
            ·
              refine ⟨2793526257047171499246883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3724701676062895332329177 2793526257047171499246883)
              ·
                refine ⟨4190289385570757248870325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2793526257047171499246883 4190289385570757248870325)
                ·
                  refine ⟨392839629897258492081593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4190289385570757248870325 392839629897258492081593)
                  ·
                    rfl

theorem cell20_860684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 2, 1, 5].length) (baseStart_860684 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_860684 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_860684 prefixEnd_860684 := by exact prefixLift 860684
  have htrace : WordTrace (prefixWord ++ tailWord_860684) baseStart_860684 baseEnd_860684 := by
    simpa [prefixWord, tailWord_860684, baseEnd_860684] using wordTrace_append hprefix tailTrace_860684
  have hstable : (prefixWord ++ tailWord_860684).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_860684).length < 2 ^ (prefixWord ++ tailWord_860684).sum := by decide
  have hdescent : baseEnd_860684 < baseStart_860684 := by decide
  rcases family_descends (prefixWord ++ tailWord_860684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_860698 : List Nat := [3, 1, 1, 3, 1, 1, 3, 7]
def baseStart_860698 : Nat := 118140960795 + 860698 * 2 ^ 59
def prefixEnd_860698 : Nat := 4983230072969 + 3 ^ 40 * 860698 * 2
def baseEnd_860698 : Nat := 130948673292912221871623

theorem tailTrace_860698 : CollatzResearch.WordTrace tailWord_860698 prefixEnd_860698 130948673292912221871623 := by
  unfold tailWord_860698
  simp only [CollatzResearch.WordTrace]
  refine ⟨7848058758961404090149687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20928156690563744240399165 7848058758961404090149687)
  ·
    refine ⟨11772088138442106135224531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7848058758961404090149687 11772088138442106135224531)
    ·
      refine ⟨17658132207663159202836797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11772088138442106135224531 17658132207663159202836797)
      ·
        refine ⟨6621799577873684701063799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17658132207663159202836797 6621799577873684701063799)
        ·
          refine ⟨9932699366810527051595699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6621799577873684701063799 9932699366810527051595699)
          ·
            refine ⟨14899049050215790577393549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9932699366810527051595699 14899049050215790577393549)
            ·
              refine ⟨5587143393830921466522581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14899049050215790577393549 5587143393830921466522581)
              ·
                refine ⟨130948673292912221871623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5587143393830921466522581 130948673292912221871623)
                ·
                  rfl

theorem cell20_860698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 7].length) (baseStart_860698 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_860698 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_860698 prefixEnd_860698 := by exact prefixLift 860698
  have htrace : WordTrace (prefixWord ++ tailWord_860698) baseStart_860698 baseEnd_860698 := by
    simpa [prefixWord, tailWord_860698, baseEnd_860698] using wordTrace_append hprefix tailTrace_860698
  have hstable : (prefixWord ++ tailWord_860698).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_860698).length < 2 ^ (prefixWord ++ tailWord_860698).sum := by decide
  have hdescent : baseEnd_860698 < baseStart_860698 := by decide
  rcases family_descends (prefixWord ++ tailWord_860698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_860701 : List Nat := [1, 4, 2, 2, 1, 3, 1, 3, 3]
def baseStart_860701 : Nat := 118140960795 + 860701 * 2 ^ 59
def prefixEnd_860701 : Nat := 4983230072969 + 3 ^ 40 * 860701 * 2
def baseEnd_860701 : Nat := 392847389160481988514857

theorem tailTrace_860701 : CollatzResearch.WordTrace tailWord_860701 prefixEnd_860701 392847389160481988514857 := by
  unfold tailWord_860701
  simp only [CollatzResearch.WordTrace]
  refine ⟨31392344454834747872957957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20928229636556498581971971 31392344454834747872957957)
  ·
    refine ⟨5886064585281515226179617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31392344454834747872957957 5886064585281515226179617)
    ·
      refine ⟨4414548438961136419634713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5886064585281515226179617 4414548438961136419634713)
      ·
        refine ⟨3310911329220852314726035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4414548438961136419634713 3310911329220852314726035)
        ·
          refine ⟨4966366993831278472089053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3310911329220852314726035 4966366993831278472089053)
          ·
            refine ⟨1862387622686729427033395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4966366993831278472089053 1862387622686729427033395)
            ·
              refine ⟨2793581434030094140550093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1862387622686729427033395 2793581434030094140550093)
              ·
                refine ⟨1047593037761285302706285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2793581434030094140550093 1047593037761285302706285)
                ·
                  refine ⟨392847389160481988514857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1047593037761285302706285 392847389160481988514857)
                  ·
                    rfl

theorem cell20_860701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 1, 3, 3].length) (baseStart_860701 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_860701 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_860701 prefixEnd_860701 := by exact prefixLift 860701
  have htrace : WordTrace (prefixWord ++ tailWord_860701) baseStart_860701 baseEnd_860701 := by
    simpa [prefixWord, tailWord_860701, baseEnd_860701] using wordTrace_append hprefix tailTrace_860701
  have hstable : (prefixWord ++ tailWord_860701).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_860701).length < 2 ^ (prefixWord ++ tailWord_860701).sum := by decide
  have hdescent : baseEnd_860701 < baseStart_860701 := by decide
  rcases family_descends (prefixWord ++ tailWord_860701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_860753 : List Nat := [1, 2, 2, 1, 3, 5, 1, 5]
def baseStart_860753 : Nat := 118140960795 + 860753 * 2 ^ 59
def prefixEnd_860753 : Nat := 4983230072969 + 3 ^ 40 * 860753 * 2
def baseEnd_860753 : Nat := 130957041125800306260437

theorem tailTrace_860753 : CollatzResearch.WordTrace tailWord_860753 prefixEnd_860753 130957041125800306260437 := by
  unfold tailWord_860753
  simp only [CollatzResearch.WordTrace]
  refine ⟨31394241050646360753850913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20929494033764240502567275 31394241050646360753850913)
  ·
    refine ⟨23545680787984770565388185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31394241050646360753850913 23545680787984770565388185)
    ·
      refine ⟨17659260590988577924041139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23545680787984770565388185 17659260590988577924041139)
      ·
        refine ⟨26488890886482866886061709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17659260590988577924041139 26488890886482866886061709)
        ·
          refine ⟨9933334082431075082273141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26488890886482866886061709 9933334082431075082273141)
          ·
            refine ⟨931250070227913288963107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9933334082431075082273141 931250070227913288963107)
            ·
              refine ⟨1396875105341869933444661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 931250070227913288963107 1396875105341869933444661)
              ·
                refine ⟨130957041125800306260437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1396875105341869933444661 130957041125800306260437)
                ·
                  rfl

theorem cell20_860753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 1, 5].length) (baseStart_860753 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_860753 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_860753 prefixEnd_860753 := by exact prefixLift 860753
  have htrace : WordTrace (prefixWord ++ tailWord_860753) baseStart_860753 baseEnd_860753 := by
    simpa [prefixWord, tailWord_860753, baseEnd_860753] using wordTrace_append hprefix tailTrace_860753
  have hstable : (prefixWord ++ tailWord_860753).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_860753).length < 2 ^ (prefixWord ++ tailWord_860753).sum := by decide
  have hdescent : baseEnd_860753 < baseStart_860753 := by decide
  rcases family_descends (prefixWord ++ tailWord_860753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_860760 : List Nat := [2, 1, 2, 2, 1, 2, 4, 3, 3]
def baseStart_860760 : Nat := 118140960795 + 860760 * 2 ^ 59
def prefixEnd_860760 : Nat := 4983230072969 + 3 ^ 40 * 860760 * 2
def baseEnd_860760 : Nat := 392874318368140005547949

theorem tailTrace_860760 : CollatzResearch.WordTrace tailWord_860760 prefixEnd_860760 392874318368140005547949 := by
  unfold tailWord_860760
  simp only [CollatzResearch.WordTrace]
  refine ⟨15697248180810500474677867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20929664241080667299570489 15697248180810500474677867)
  ·
    refine ⟨23545872271215750712016801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15697248180810500474677867 23545872271215750712016801)
    ·
      refine ⟨17659404203411813034012601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23545872271215750712016801 17659404203411813034012601)
      ·
        refine ⟨13244553152558859775509451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17659404203411813034012601 13244553152558859775509451)
        ·
          refine ⟨19866829728838289663264177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13244553152558859775509451 19866829728838289663264177)
          ·
            refine ⟨14900122296628717247448133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19866829728838289663264177 14900122296628717247448133)
            ·
              refine ⟨2793772930617884483896525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14900122296628717247448133 2793772930617884483896525)
              ·
                refine ⟨1047664848981706681461197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2793772930617884483896525 1047664848981706681461197)
                ·
                  refine ⟨392874318368140005547949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1047664848981706681461197 392874318368140005547949)
                  ·
                    rfl

theorem cell20_860760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 4, 3, 3].length) (baseStart_860760 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_860760 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_860760 prefixEnd_860760 := by exact prefixLift 860760
  have htrace : WordTrace (prefixWord ++ tailWord_860760) baseStart_860760 baseEnd_860760 := by
    simpa [prefixWord, tailWord_860760, baseEnd_860760] using wordTrace_append hprefix tailTrace_860760
  have hstable : (prefixWord ++ tailWord_860760).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_860760).length < 2 ^ (prefixWord ++ tailWord_860760).sum := by decide
  have hdescent : baseEnd_860760 < baseStart_860760 := by decide
  rcases family_descends (prefixWord ++ tailWord_860760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_860805 : List Nat := [1, 3, 1, 1, 4, 2, 1, 3, 4]
def baseStart_860805 : Nat := 118140960795 + 860805 * 2 ^ 59
def prefixEnd_860805 : Nat := 4983230072969 + 3 ^ 40 * 860805 * 2
def baseEnd_860805 : Nat := 392894857594319849047765

theorem tailTrace_860805 : CollatzResearch.WordTrace tailWord_860805 prefixEnd_860805 392894857594319849047765 := by
  unfold tailWord_860805
  simp only [CollatzResearch.WordTrace]
  refine ⟨31396137646457973634743869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20930758430971982423162579 31396137646457973634743869)
  ·
    refine ⟨11773551617421740113028951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31396137646457973634743869 11773551617421740113028951)
    ·
      refine ⟨17660327426132610169543427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11773551617421740113028951 17660327426132610169543427)
      ·
        refine ⟨26490491139198915254315141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17660327426132610169543427 26490491139198915254315141)
        ·
          refine ⟨4966967088599796610184089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26490491139198915254315141 4966967088599796610184089)
          ·
            refine ⟨3725225316449847457638067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4966967088599796610184089 3725225316449847457638067)
            ·
              refine ⟨5587837974674771186457101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3725225316449847457638067 5587837974674771186457101)
              ·
                refine ⟨2095439240503039194921413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5587837974674771186457101 2095439240503039194921413)
                ·
                  refine ⟨392894857594319849047765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2095439240503039194921413 392894857594319849047765)
                  ·
                    rfl

theorem cell20_860805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 3, 4].length) (baseStart_860805 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_860805 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_860805 prefixEnd_860805 := by exact prefixLift 860805
  have htrace : WordTrace (prefixWord ++ tailWord_860805) baseStart_860805 baseEnd_860805 := by
    simpa [prefixWord, tailWord_860805, baseEnd_860805] using wordTrace_append hprefix tailTrace_860805
  have hstable : (prefixWord ++ tailWord_860805).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_860805).length < 2 ^ (prefixWord ++ tailWord_860805).sum := by decide
  have hdescent : baseEnd_860805 < baseStart_860805 := by decide
  rcases family_descends (prefixWord ++ tailWord_860805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_860829 : List Nat := [1, 4, 2, 1, 1, 1, 6, 4]
def baseStart_860829 : Nat := 118140960795 + 860829 * 2 ^ 59
def prefixEnd_860829 : Nat := 4983230072969 + 3 ^ 40 * 860829 * 2
def baseEnd_860829 : Nat := 130968603949427477415889

theorem tailTrace_860829 : CollatzResearch.WordTrace tailWord_860829 prefixEnd_860829 130968603949427477415889 := by
  unfold tailWord_860829
  simp only [CollatzResearch.WordTrace]
  refine ⟨31397012998371025733617541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20931341998914017155745027 31397012998371025733617541)
  ·
    refine ⟨5886939937194567325053289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31397012998371025733617541 5886939937194567325053289)
    ·
      refine ⟨4415204952895925493789967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5886939937194567325053289 4415204952895925493789967)
      ·
        refine ⟨6622807429343888240684951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4415204952895925493789967 6622807429343888240684951)
        ·
          refine ⟨9934211144015832361027427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6622807429343888240684951 9934211144015832361027427)
          ·
            refine ⟨14901316716023748541541141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9934211144015832361027427 14901316716023748541541141)
            ·
              refine ⟨698499221063613212884741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 14901316716023748541541141 698499221063613212884741)
              ·
                refine ⟨130968603949427477415889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 698499221063613212884741 130968603949427477415889)
                ·
                  rfl

theorem cell20_860829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 6, 4].length) (baseStart_860829 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_860829 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_860829 prefixEnd_860829 := by exact prefixLift 860829
  have htrace : WordTrace (prefixWord ++ tailWord_860829) baseStart_860829 baseEnd_860829 := by
    simpa [prefixWord, tailWord_860829, baseEnd_860829] using wordTrace_append hprefix tailTrace_860829
  have hstable : (prefixWord ++ tailWord_860829).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_860829).length < 2 ^ (prefixWord ++ tailWord_860829).sum := by decide
  have hdescent : baseEnd_860829 < baseStart_860829 := by decide
  rcases family_descends (prefixWord ++ tailWord_860829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_860846 : List Nat := [4, 1, 4, 1, 1, 3, 6]
def baseStart_860846 : Nat := 118140960795 + 860846 * 2 ^ 59
def prefixEnd_860846 : Nat := 4983230072969 + 3 ^ 40 * 860846 * 2
def baseEnd_860846 : Nat := 43657063456833992075659

theorem tailTrace_860846 : CollatzResearch.WordTrace tailWord_860846 prefixEnd_860846 43657063456833992075659 := by
  unfold tailWord_860846
  simp only [CollatzResearch.WordTrace]
  refine ⟨3924704129913679704623299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20931755359539625091324261 3924704129913679704623299)
  ·
    refine ⟨5887056194870519556934949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3924704129913679704623299 5887056194870519556934949)
    ·
      refine ⟨1103823036538222416925303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5887056194870519556934949 1103823036538222416925303)
      ·
        refine ⟨1655734554807333625387955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1103823036538222416925303 1655734554807333625387955)
        ·
          refine ⟨2483601832211000438081933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1655734554807333625387955 2483601832211000438081933)
          ·
            refine ⟨931350687079125164280725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2483601832211000438081933 931350687079125164280725)
            ·
              refine ⟨43657063456833992075659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 931350687079125164280725 43657063456833992075659)
              ·
                rfl

theorem cell20_860846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 6].length) (baseStart_860846 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_860846 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_860846 prefixEnd_860846 := by exact prefixLift 860846
  have htrace : WordTrace (prefixWord ++ tailWord_860846) baseStart_860846 baseEnd_860846 := by
    simpa [prefixWord, tailWord_860846, baseEnd_860846] using wordTrace_append hprefix tailTrace_860846
  have hstable : (prefixWord ++ tailWord_860846).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_860846).length < 2 ^ (prefixWord ++ tailWord_860846).sum := by decide
  have hdescent : baseEnd_860846 < baseStart_860846 := by decide
  rcases family_descends (prefixWord ++ tailWord_860846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_860888 : List Nat := [2, 1, 2, 2, 3, 2, 2, 6]
def baseStart_860888 : Nat := 118140960795 + 860888 * 2 ^ 59
def prefixEnd_860888 : Nat := 4983230072969 + 3 ^ 40 * 860888 * 2
def baseEnd_860888 : Nat := 130977580351980149760253

theorem tailTrace_860888 : CollatzResearch.WordTrace tailWord_860888 prefixEnd_860888 130977580351980149760253 := by
  unfold tailWord_860888
  simp only [CollatzResearch.WordTrace]
  refine ⟨15699582452578639405007659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20932776603438185873343545 15699582452578639405007659)
  ·
    refine ⟨23549373678867959107511489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15699582452578639405007659 23549373678867959107511489)
    ·
      refine ⟨17662030259150969330633617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23549373678867959107511489 17662030259150969330633617)
      ·
        refine ⟨13246522694363226997975213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17662030259150969330633617 13246522694363226997975213)
        ·
          refine ⟨4967446010386210124240705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13246522694363226997975213 4967446010386210124240705)
          ·
            refine ⟨3725584507789657593180529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4967446010386210124240705 3725584507789657593180529)
            ·
              refine ⟨2794188380842243194885397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3725584507789657593180529 2794188380842243194885397)
              ·
                refine ⟨130977580351980149760253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2794188380842243194885397 130977580351980149760253)
                ·
                  rfl

theorem cell20_860888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 2, 6].length) (baseStart_860888 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_860888 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_860888 prefixEnd_860888 := by exact prefixLift 860888
  have htrace : WordTrace (prefixWord ++ tailWord_860888) baseStart_860888 baseEnd_860888 := by
    simpa [prefixWord, tailWord_860888, baseEnd_860888] using wordTrace_append hprefix tailTrace_860888
  have hstable : (prefixWord ++ tailWord_860888).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_860888).length < 2 ^ (prefixWord ++ tailWord_860888).sum := by decide
  have hdescent : baseEnd_860888 < baseStart_860888 := by decide
  rcases family_descends (prefixWord ++ tailWord_860888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_860912 : List Nat := [2, 1, 1, 1, 3, 1, 6, 2, 3]
def baseStart_860912 : Nat := 118140960795 + 860912 * 2 ^ 59
def prefixEnd_860912 : Nat := 4983230072969 + 3 ^ 40 * 860912 * 2
def baseEnd_860912 : Nat := 392943695309903032480661

theorem tailTrace_860912 : CollatzResearch.WordTrace tailWord_860912 prefixEnd_860912 392943695309903032480661 := by
  unfold tailWord_860912
  simp only [CollatzResearch.WordTrace]
  refine ⟨15700020128535165454444495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20933360171380220605925993 15700020128535165454444495)
  ·
    refine ⟨23550030192802748181666743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15700020128535165454444495 23550030192802748181666743)
    ·
      refine ⟨35325045289204122272500115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23550030192802748181666743 35325045289204122272500115)
      ·
        refine ⟨52987567933806183408750173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35325045289204122272500115 52987567933806183408750173)
        ·
          refine ⟨19870337975177318778281315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52987567933806183408750173 19870337975177318778281315)
          ·
            refine ⟨29805506962765978167421973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19870337975177318778281315 29805506962765978167421973)
            ·
              refine ⟨1397133138879655226597905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 29805506962765978167421973 1397133138879655226597905)
              ·
                refine ⟨1047849854159741419948429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1397133138879655226597905 1047849854159741419948429)
                ·
                  refine ⟨392943695309903032480661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1047849854159741419948429 392943695309903032480661)
                  ·
                    rfl

theorem cell20_860912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 6, 2, 3].length) (baseStart_860912 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_860912 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_860912 prefixEnd_860912 := by exact prefixLift 860912
  have htrace : WordTrace (prefixWord ++ tailWord_860912) baseStart_860912 baseEnd_860912 := by
    simpa [prefixWord, tailWord_860912, baseEnd_860912] using wordTrace_append hprefix tailTrace_860912
  have hstable : (prefixWord ++ tailWord_860912).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_860912).length < 2 ^ (prefixWord ++ tailWord_860912).sum := by decide
  have hdescent : baseEnd_860912 < baseStart_860912 := by decide
  rcases family_descends (prefixWord ++ tailWord_860912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_860974 : List Nat := [4, 1, 3, 2, 1, 1, 1, 3, 4]
def baseStart_860974 : Nat := 118140960795 + 860974 * 2 ^ 59
def prefixEnd_860974 : Nat := 4983230072969 + 3 ^ 40 * 860974 * 2
def baseEnd_860974 : Nat := 392971993799306372413741

theorem tailTrace_860974 : CollatzResearch.WordTrace tailWord_860974 prefixEnd_860974 392971993799306372413741 := by
  unfold tailWord_860974
  simp only [CollatzResearch.WordTrace]
  refine ⟨3925287697855714437205747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20934867721897143665097317 3925287697855714437205747)
  ·
    refine ⟨5887931546783571655808621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3925287697855714437205747 5887931546783571655808621)
    ·
      refine ⟨2207974330043839370928233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5887931546783571655808621 2207974330043839370928233)
      ·
        refine ⟨1655980747532879528196175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2207974330043839370928233 1655980747532879528196175)
        ·
          refine ⟨2483971121299319292294263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1655980747532879528196175 2483971121299319292294263)
          ·
            refine ⟨3725956681948978938441395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2483971121299319292294263 3725956681948978938441395)
            ·
              refine ⟨5588935022923468407662093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3725956681948978938441395 5588935022923468407662093)
              ·
                refine ⟨2095850633596300652873285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5588935022923468407662093 2095850633596300652873285)
                ·
                  refine ⟨392971993799306372413741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2095850633596300652873285 392971993799306372413741)
                  ·
                    rfl

theorem cell20_860974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 3, 4].length) (baseStart_860974 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_860974 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_860974 prefixEnd_860974 := by exact prefixLift 860974
  have htrace : WordTrace (prefixWord ++ tailWord_860974) baseStart_860974 baseEnd_860974 := by
    simpa [prefixWord, tailWord_860974, baseEnd_860974] using wordTrace_append hprefix tailTrace_860974
  have hstable : (prefixWord ++ tailWord_860974).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_860974).length < 2 ^ (prefixWord ++ tailWord_860974).sum := by decide
  have hdescent : baseEnd_860974 < baseStart_860974 := by decide
  rcases family_descends (prefixWord ++ tailWord_860974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_861016 : List Nat := [2, 1, 2, 2, 1, 1, 1, 4, 6]
def baseStart_861016 : Nat := 118140960795 + 861016 * 2 ^ 59
def prefixEnd_861016 : Nat := 4983230072969 + 3 ^ 40 * 861016 * 2
def baseEnd_861016 : Nat := 392991163743740893013569

theorem tailTrace_861016 : CollatzResearch.WordTrace tailWord_861016 prefixEnd_861016 392991163743740893013569 := by
  unfold tailWord_861016
  simp only [CollatzResearch.WordTrace]
  refine ⟨15701916724346778335337451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20935888965795704447116601 15701916724346778335337451)
  ·
    refine ⟨23552875086520167503006177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15701916724346778335337451 23552875086520167503006177)
    ·
      refine ⟨17664656314890125627254633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23552875086520167503006177 17664656314890125627254633)
      ·
        refine ⟨13248492236167594220440975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17664656314890125627254633 13248492236167594220440975)
        ·
          refine ⟨19872738354251391330661463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13248492236167594220440975 19872738354251391330661463)
          ·
            refine ⟨29809107531377086995992195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19872738354251391330661463 29809107531377086995992195)
            ·
              refine ⟨44713661297065630493988293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29809107531377086995992195 44713661297065630493988293)
              ·
                refine ⟨8383811493199805717622805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44713661297065630493988293 8383811493199805717622805)
                ·
                  refine ⟨392991163743740893013569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8383811493199805717622805 392991163743740893013569)
                  ·
                    rfl

theorem cell20_861016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 4, 6].length) (baseStart_861016 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_861016 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_861016 prefixEnd_861016 := by exact prefixLift 861016
  have htrace : WordTrace (prefixWord ++ tailWord_861016) baseStart_861016 baseEnd_861016 := by
    simpa [prefixWord, tailWord_861016, baseEnd_861016] using wordTrace_append hprefix tailTrace_861016
  have hstable : (prefixWord ++ tailWord_861016).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_861016).length < 2 ^ (prefixWord ++ tailWord_861016).sum := by decide
  have hdescent : baseEnd_861016 < baseStart_861016 := by decide
  rcases family_descends (prefixWord ++ tailWord_861016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_861109 : List Nat := [1, 3, 3, 2, 1, 1, 3, 2, 4]
def baseStart_861109 : Nat := 118140960795 + 861109 * 2 ^ 59
def prefixEnd_861109 : Nat := 4983230072969 + 3 ^ 40 * 861109 * 2
def baseEnd_861109 : Nat := 393033611477845902913189

theorem tailTrace_861109 : CollatzResearch.WordTrace tailWord_861109 prefixEnd_861109 393033611477845902913189 := by
  unfold tailWord_861109
  simp only [CollatzResearch.WordTrace]
  refine ⟨31407225437356633553810381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20938150291571089035873587 31407225437356633553810381)
  ·
    refine ⟨11777709539008737582678893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31407225437356633553810381 11777709539008737582678893)
    ·
      refine ⟨4416641077128276593504585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11777709539008737582678893 4416641077128276593504585)
      ·
        refine ⟨3312480807846207445128439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4416641077128276593504585 3312480807846207445128439)
        ·
          refine ⟨4968721211769311167692659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3312480807846207445128439 4968721211769311167692659)
          ·
            refine ⟨7453081817653966751538989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4968721211769311167692659 7453081817653966751538989)
            ·
              refine ⟨2794905681620237531827121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7453081817653966751538989 2794905681620237531827121)
              ·
                refine ⟨2096179261215178148870341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2794905681620237531827121 2096179261215178148870341)
                ·
                  refine ⟨393033611477845902913189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2096179261215178148870341 393033611477845902913189)
                  ·
                    rfl

theorem cell20_861109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 3, 2, 4].length) (baseStart_861109 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_861109 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_861109 prefixEnd_861109 := by exact prefixLift 861109
  have htrace : WordTrace (prefixWord ++ tailWord_861109) baseStart_861109 baseEnd_861109 := by
    simpa [prefixWord, tailWord_861109, baseEnd_861109] using wordTrace_append hprefix tailTrace_861109
  have hstable : (prefixWord ++ tailWord_861109).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_861109).length < 2 ^ (prefixWord ++ tailWord_861109).sum := by decide
  have hdescent : baseEnd_861109 < baseStart_861109 := by decide
  rcases family_descends (prefixWord ++ tailWord_861109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_861130 : List Nat := [3, 1, 2, 1, 2, 1, 1, 1, 8]
def baseStart_861130 : Nat := 118140960795 + 861130 * 2 ^ 59
def prefixEnd_861130 : Nat := 4983230072969 + 3 ^ 40 * 861130 * 2
def baseEnd_861130 : Nat := 393043196450063163213103

theorem tailTrace_861130 : CollatzResearch.WordTrace tailWord_861130 prefixEnd_861130 393043196450063163213103 := by
  unfold tailWord_861130
  simp only [CollatzResearch.WordTrace]
  refine ⟨7851997842570138535081211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20938660913520369426883229 7851997842570138535081211)
  ·
    refine ⟨11777996763855207802621817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7851997842570138535081211 11777996763855207802621817)
    ·
      refine ⟨8833497572891405851966363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11777996763855207802621817 8833497572891405851966363)
      ·
        refine ⟨13250246359337108777949545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8833497572891405851966363 13250246359337108777949545)
        ·
          refine ⟨9937684769502831583462159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13250246359337108777949545 9937684769502831583462159)
          ·
            refine ⟨14906527154254247375193239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9937684769502831583462159 14906527154254247375193239)
            ·
              refine ⟨22359790731381371062789859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14906527154254247375193239 22359790731381371062789859)
              ·
                refine ⟨33539686097072056594184789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22359790731381371062789859 33539686097072056594184789)
                ·
                  refine ⟨393043196450063163213103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 33539686097072056594184789 393043196450063163213103)
                  ·
                    rfl

theorem cell20_861130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 1, 8].length) (baseStart_861130 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_861130 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_861130 prefixEnd_861130 := by exact prefixLift 861130
  have htrace : WordTrace (prefixWord ++ tailWord_861130) baseStart_861130 baseEnd_861130 := by
    simpa [prefixWord, tailWord_861130, baseEnd_861130] using wordTrace_append hprefix tailTrace_861130
  have hstable : (prefixWord ++ tailWord_861130).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_861130).length < 2 ^ (prefixWord ++ tailWord_861130).sum := by decide
  have hdescent : baseEnd_861130 < baseStart_861130 := by decide
  rcases family_descends (prefixWord ++ tailWord_861130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_861137 : List Nat := [1, 2, 2, 1, 2, 1, 11]
def baseStart_861137 : Nat := 118140960795 + 861137 * 2 ^ 59
def prefixEnd_861137 : Nat := 4983230072969 + 3 ^ 40 * 861137 * 2
def baseEnd_861137 : Nat := 43671821271200249997749

theorem tailTrace_861137 : CollatzResearch.WordTrace tailWord_861137 prefixEnd_861137 43671821271200249997749 := by
  unfold tailWord_861137
  simp only [CollatzResearch.WordTrace]
  refine ⟨31408246681255194335829665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20938831120836796223886443 31408246681255194335829665)
  ·
    refine ⟨23556185010941395751872249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31408246681255194335829665 23556185010941395751872249)
    ·
      refine ⟨17667138758206046813904187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23556185010941395751872249 17667138758206046813904187)
      ·
        refine ⟨26500708137309070220856281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17667138758206046813904187 26500708137309070220856281)
        ·
          refine ⟨19875531102981802665642211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26500708137309070220856281 19875531102981802665642211)
          ·
            refine ⟨29813296654472703998463317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19875531102981802665642211 29813296654472703998463317)
            ·
              refine ⟨43671821271200249997749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 29813296654472703998463317 43671821271200249997749)
              ·
                rfl

theorem cell20_861137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 11].length) (baseStart_861137 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_861137 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_861137 prefixEnd_861137 := by exact prefixLift 861137
  have htrace : WordTrace (prefixWord ++ tailWord_861137) baseStart_861137 baseEnd_861137 := by
    simpa [prefixWord, tailWord_861137, baseEnd_861137] using wordTrace_append hprefix tailTrace_861137
  have hstable : (prefixWord ++ tailWord_861137).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_861137).length < 2 ^ (prefixWord ++ tailWord_861137).sum := by decide
  have hdescent : baseEnd_861137 < baseStart_861137 := by decide
  rcases family_descends (prefixWord ++ tailWord_861137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_861140 : List Nat := [2, 4, 1, 2, 1, 3, 1, 1, 5]
def baseStart_861140 : Nat := 118140960795 + 861140 * 2 ^ 59
def prefixEnd_861140 : Nat := 4983230072969 + 3 ^ 40 * 861140 * 2
def baseEnd_861140 : Nat := 393047760722547572879729

theorem tailTrace_861140 : CollatzResearch.WordTrace tailWord_861140 prefixEnd_861140 393047760722547572879729 := by
  unfold tailWord_861140
  simp only [CollatzResearch.WordTrace]
  refine ⟨15704178050122162924094437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20938904066829550565459249 15704178050122162924094437)
  ·
    refine ⟨2944533384397905548267707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15704178050122162924094437 2944533384397905548267707)
    ·
      refine ⟨4416800076596858322401561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2944533384397905548267707 4416800076596858322401561)
      ·
        refine ⟨3312600057447643741801171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4416800076596858322401561 3312600057447643741801171)
        ·
          refine ⟨4968900086171465612701757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3312600057447643741801171 4968900086171465612701757)
          ·
            refine ⟨1863337532314299604763159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4968900086171465612701757 1863337532314299604763159)
            ·
              refine ⟨2795006298471449407144739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1863337532314299604763159 2795006298471449407144739)
              ·
                refine ⟨4192509447707174110717109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2795006298471449407144739 4192509447707174110717109)
                ·
                  refine ⟨393047760722547572879729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4192509447707174110717109 393047760722547572879729)
                  ·
                    rfl

theorem cell20_861140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 1, 1, 5].length) (baseStart_861140 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_861140 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_861140 prefixEnd_861140 := by exact prefixLift 861140
  have htrace : WordTrace (prefixWord ++ tailWord_861140) baseStart_861140 baseEnd_861140 := by
    simpa [prefixWord, tailWord_861140, baseEnd_861140] using wordTrace_append hprefix tailTrace_861140
  have hstable : (prefixWord ++ tailWord_861140).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_861140).length < 2 ^ (prefixWord ++ tailWord_861140).sum := by decide
  have hdescent : baseEnd_861140 < baseStart_861140 := by decide
  rcases family_descends (prefixWord ++ tailWord_861140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_861192 : List Nat := [2, 1, 3, 2, 1, 5, 6]
def baseStart_861192 : Nat := 118140960795 + 861192 * 2 ^ 59
def prefixEnd_861192 : Nat := 4983230072969 + 3 ^ 40 * 861192 * 2
def baseEnd_861192 : Nat := 43674610548829611460687

theorem tailTrace_861192 : CollatzResearch.WordTrace tailWord_861192 prefixEnd_861192 43674610548829611460687 := by
  unfold tailWord_861192
  simp only [CollatzResearch.WordTrace]
  refine ⟨15705126348027969364540915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20940168464037292486054553 15705126348027969364540915)
  ·
    refine ⟨23557689522041954046811373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15705126348027969364540915 23557689522041954046811373)
    ·
      refine ⟨8834133570765732767554265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23557689522041954046811373 8834133570765732767554265)
      ·
        refine ⟨6625600178074299575665699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8834133570765732767554265 6625600178074299575665699)
        ·
          refine ⟨9938400267111449363498549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6625600178074299575665699 9938400267111449363498549)
          ·
            refine ⟨931725025041698377827989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9938400267111449363498549 931725025041698377827989)
            ·
              refine ⟨43674610548829611460687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 931725025041698377827989 43674610548829611460687)
              ·
                rfl

theorem cell20_861192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 6].length) (baseStart_861192 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_861192 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_861192 prefixEnd_861192 := by exact prefixLift 861192
  have htrace : WordTrace (prefixWord ++ tailWord_861192) baseStart_861192 baseEnd_861192 := by
    simpa [prefixWord, tailWord_861192, baseEnd_861192] using wordTrace_append hprefix tailTrace_861192
  have hstable : (prefixWord ++ tailWord_861192).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_861192).length < 2 ^ (prefixWord ++ tailWord_861192).sum := by decide
  have hdescent : baseEnd_861192 < baseStart_861192 := by decide
  rcases family_descends (prefixWord ++ tailWord_861192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_861212 : List Nat := [2, 2, 3, 1, 4, 2, 2, 1, 3]
def baseStart_861212 : Nat := 118140960795 + 861212 * 2 ^ 59
def prefixEnd_861212 : Nat := 4983230072969 + 3 ^ 40 * 861212 * 2
def baseEnd_861212 : Nat := 393080623484435322479435

theorem tailTrace_861212 : CollatzResearch.WordTrace tailWord_861212 prefixEnd_861212 393080623484435322479435 := by
  unfold tailWord_861212
  simp only [CollatzResearch.WordTrace]
  refine ⟨15705491077991741072404945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20940654770655654763206593 15705491077991741072404945)
  ·
    refine ⟨11779118308493805804303709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15705491077991741072404945 11779118308493805804303709)
    ·
      refine ⟨4417169365685177176613891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11779118308493805804303709 4417169365685177176613891)
      ·
        refine ⟨6625754048527765764920837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4417169365685177176613891 6625754048527765764920837)
        ·
          refine ⟨1242328884098956080922657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6625754048527765764920837 1242328884098956080922657)
          ·
            refine ⟨931746663074217060691993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1242328884098956080922657 931746663074217060691993)
            ·
              refine ⟨698809997305662795518995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 931746663074217060691993 698809997305662795518995)
              ·
                refine ⟨1048214995958494193278493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 698809997305662795518995 1048214995958494193278493)
                ·
                  refine ⟨393080623484435322479435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1048214995958494193278493 393080623484435322479435)
                  ·
                    rfl

theorem cell20_861212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 2, 1, 3].length) (baseStart_861212 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_861212 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_861212 prefixEnd_861212 := by exact prefixLift 861212
  have htrace : WordTrace (prefixWord ++ tailWord_861212) baseStart_861212 baseEnd_861212 := by
    simpa [prefixWord, tailWord_861212, baseEnd_861212] using wordTrace_append hprefix tailTrace_861212
  have hstable : (prefixWord ++ tailWord_861212).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_861212).length < 2 ^ (prefixWord ++ tailWord_861212).sum := by decide
  have hdescent : baseEnd_861212 < baseStart_861212 := by decide
  rcases family_descends (prefixWord ++ tailWord_861212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_861230 : List Nat := [4, 1, 3, 1, 1, 1, 1, 8]
def baseStart_861230 : Nat := 118140960795 + 861230 * 2 ^ 59
def prefixEnd_861230 : Nat := 4983230072969 + 3 ^ 40 * 861230 * 2
def baseEnd_861230 : Nat := 131029613058302419959787

theorem tailTrace_861230 : CollatzResearch.WordTrace tailWord_861230 prefixEnd_861230 131029613058302419959787 := by
  unfold tailWord_861230
  simp only [CollatzResearch.WordTrace]
  refine ⟨3926454833739783902370643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20941092446612180812643429 3926454833739783902370643)
  ·
    refine ⟨5889682250609675853555965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3926454833739783902370643 5889682250609675853555965)
    ·
      refine ⟨2208630843978628445083487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5889682250609675853555965 2208630843978628445083487)
      ·
        refine ⟨3312946265967942667625231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2208630843978628445083487 3312946265967942667625231)
        ·
          refine ⟨4969419398951914001437847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3312946265967942667625231 4969419398951914001437847)
          ·
            refine ⟨7454129098427871002156771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4969419398951914001437847 7454129098427871002156771)
            ·
              refine ⟨11181193647641806503235157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7454129098427871002156771 11181193647641806503235157)
              ·
                refine ⟨131029613058302419959787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11181193647641806503235157 131029613058302419959787)
                ·
                  rfl

theorem cell20_861230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 8].length) (baseStart_861230 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_861230 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_861230 prefixEnd_861230 := by exact prefixLift 861230
  have htrace : WordTrace (prefixWord ++ tailWord_861230) baseStart_861230 baseEnd_861230 := by
    simpa [prefixWord, tailWord_861230, baseEnd_861230] using wordTrace_append hprefix tailTrace_861230
  have hstable : (prefixWord ++ tailWord_861230).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_861230).length < 2 ^ (prefixWord ++ tailWord_861230).sum := by decide
  have hdescent : baseEnd_861230 < baseStart_861230 := by decide
  rcases family_descends (prefixWord ++ tailWord_861230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_861268 : List Nat := [2, 4, 1, 1, 1, 1, 5, 5]
def baseStart_861268 : Nat := 118140960795 + 861268 * 2 ^ 59
def prefixEnd_861268 : Nat := 4983230072969 + 3 ^ 40 * 861268 * 2
def baseEnd_861268 : Nat := 131035394470116005537513

theorem tailTrace_861268 : CollatzResearch.WordTrace tailWord_861268 prefixEnd_861268 131035394470116005537513 := by
  unfold tailWord_861268
  simp only [CollatzResearch.WordTrace]
  refine ⟨15706512321890301854424229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20942016429187069139232305 15706512321890301854424229)
  ·
    refine ⟨2944971060354431597704543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15706512321890301854424229 2944971060354431597704543)
    ·
      refine ⟨4417456590531647396556815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2944971060354431597704543 4417456590531647396556815)
      ·
        refine ⟨6626184885797471094835223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4417456590531647396556815 6626184885797471094835223)
        ·
          refine ⟨9939277328696206642252835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6626184885797471094835223 9939277328696206642252835)
          ·
            refine ⟨14908915993044309963379253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9939277328696206642252835 14908915993044309963379253)
            ·
              refine ⟨1397710874347904059066805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14908915993044309963379253 1397710874347904059066805)
              ·
                refine ⟨131035394470116005537513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1397710874347904059066805 131035394470116005537513)
                ·
                  rfl

theorem cell20_861268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 5, 5].length) (baseStart_861268 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_861268 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_861268 prefixEnd_861268 := by exact prefixLift 861268
  have htrace : WordTrace (prefixWord ++ tailWord_861268) baseStart_861268 baseEnd_861268 := by
    simpa [prefixWord, tailWord_861268, baseEnd_861268] using wordTrace_append hprefix tailTrace_861268
  have hstable : (prefixWord ++ tailWord_861268).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_861268).length < 2 ^ (prefixWord ++ tailWord_861268).sum := by decide
  have hdescent : baseEnd_861268 < baseStart_861268 := by decide
  rcases family_descends (prefixWord ++ tailWord_861268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_861316 : List Nat := [2, 3, 2, 1, 2, 2, 2, 4, 2]
def baseStart_861316 : Nat := 118140960795 + 861316 * 2 ^ 59
def prefixEnd_861316 : Nat := 4983230072969 + 3 ^ 40 * 861316 * 2
def baseEnd_861316 : Nat := 393128091918273183012343

theorem tailTrace_861316 : CollatzResearch.WordTrace tailWord_861316 prefixEnd_861316 393128091918273183012343 := by
  unfold tailWord_861316
  simp only [CollatzResearch.WordTrace]
  refine ⟨15707387673803353953297901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20943183565071138604397201 15707387673803353953297901)
  ·
    refine ⟨5890270377676257732486713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15707387673803353953297901 5890270377676257732486713)
    ·
      refine ⟨4417702783257193299365035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5890270377676257732486713 4417702783257193299365035)
      ·
        refine ⟨6626554174885789949047553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4417702783257193299365035 6626554174885789949047553)
        ·
          refine ⟨4969915631164342461785665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6626554174885789949047553 4969915631164342461785665)
          ·
            refine ⟨3727436723373256846339249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4969915631164342461785665 3727436723373256846339249)
            ·
              refine ⟨2795577542529942634754437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3727436723373256846339249 2795577542529942634754437)
              ·
                refine ⟨524170789224364244016457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2795577542529942634754437 524170789224364244016457)
                ·
                  refine ⟨393128091918273183012343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 524170789224364244016457 393128091918273183012343)
                  ·
                    rfl

theorem cell20_861316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 2, 4, 2].length) (baseStart_861316 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_861316 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_861316 prefixEnd_861316 := by exact prefixLift 861316
  have htrace : WordTrace (prefixWord ++ tailWord_861316) baseStart_861316 baseEnd_861316 := by
    simpa [prefixWord, tailWord_861316, baseEnd_861316] using wordTrace_append hprefix tailTrace_861316
  have hstable : (prefixWord ++ tailWord_861316).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_861316).length < 2 ^ (prefixWord ++ tailWord_861316).sum := by decide
  have hdescent : baseEnd_861316 < baseStart_861316 := by decide
  rcases family_descends (prefixWord ++ tailWord_861316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_861375 : List Nat := [1, 1, 2, 2, 2, 2, 2, 6, 2]
def baseStart_861375 : Nat := 118140960795 + 861375 * 2 ^ 59
def prefixEnd_861375 : Nat := 4983230072969 + 3 ^ 40 * 861375 * 2
def baseEnd_861375 : Nat := 393155021125931200045435

theorem tailTrace_861375 : CollatzResearch.WordTrace tailWord_861375 prefixEnd_861375 393155021125931200045435 := by
  unfold tailWord_861375
  simp only [CollatzResearch.WordTrace]
  refine ⟨31416927254392960982993579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20944618169595307321995719 31416927254392960982993579)
  ·
    refine ⟨47125390881589441474490369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31416927254392960982993579 47125390881589441474490369)
    ·
      refine ⟨35344043161192081105867777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47125390881589441474490369 35344043161192081105867777)
      ·
        refine ⟨26508032370894060829400833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35344043161192081105867777 26508032370894060829400833)
        ·
          refine ⟨19881024278170545622050625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26508032370894060829400833 19881024278170545622050625)
          ·
            refine ⟨14910768208627909216537969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19881024278170545622050625 14910768208627909216537969)
            ·
              refine ⟨11183076156470931912403477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14910768208627909216537969 11183076156470931912403477)
              ·
                refine ⟨524206694834574933393913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 11183076156470931912403477 524206694834574933393913)
                ·
                  refine ⟨393155021125931200045435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 524206694834574933393913 393155021125931200045435)
                  ·
                    rfl

theorem cell20_861375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 6, 2].length) (baseStart_861375 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_861375 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_861375 prefixEnd_861375 := by exact prefixLift 861375
  have htrace : WordTrace (prefixWord ++ tailWord_861375) baseStart_861375 baseEnd_861375 := by
    simpa [prefixWord, tailWord_861375, baseEnd_861375] using wordTrace_append hprefix tailTrace_861375
  have hstable : (prefixWord ++ tailWord_861375).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_861375).length < 2 ^ (prefixWord ++ tailWord_861375).sum := by decide
  have hdescent : baseEnd_861375 < baseStart_861375 := by decide
  rcases family_descends (prefixWord ++ tailWord_861375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_861426 : List Nat := [3, 2, 1, 3, 3, 2, 2, 2, 2]
def baseStart_861426 : Nat := 118140960795 + 861426 * 2 ^ 59
def prefixEnd_861426 : Nat := 4983230072969 + 3 ^ 40 * 861426 * 2
def baseEnd_861426 : Nat := 393178298915601689345227

theorem tailTrace_861426 : CollatzResearch.WordTrace tailWord_861426 prefixEnd_861426 393178298915601689345227 := by
  unfold tailWord_861426
  simp only [CollatzResearch.WordTrace]
  refine ⟨7854696844302049173275033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20945858251472131128733421 7854696844302049173275033)
  ·
    refine ⟨5891022633226536879956275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7854696844302049173275033 5891022633226536879956275)
    ·
      refine ⟨8836533949839805319934413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5891022633226536879956275 8836533949839805319934413)
      ·
        refine ⟨3313700231189926994975405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8836533949839805319934413 3313700231189926994975405)
        ·
          refine ⟨1242637586696222623115777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3313700231189926994975405 1242637586696222623115777)
          ·
            refine ⟨931978190022166967336833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1242637586696222623115777 931978190022166967336833)
            ·
              refine ⟨698983642516625225502625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 931978190022166967336833 698983642516625225502625)
              ·
                refine ⟨524237731887468919126969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 698983642516625225502625 524237731887468919126969)
                ·
                  refine ⟨393178298915601689345227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 524237731887468919126969 393178298915601689345227)
                  ·
                    rfl

theorem cell20_861426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 2, 2, 2].length) (baseStart_861426 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_861426 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_861426 prefixEnd_861426 := by exact prefixLift 861426
  have htrace : WordTrace (prefixWord ++ tailWord_861426) baseStart_861426 baseEnd_861426 := by
    simpa [prefixWord, tailWord_861426, baseEnd_861426] using wordTrace_append hprefix tailTrace_861426
  have hstable : (prefixWord ++ tailWord_861426).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_861426).length < 2 ^ (prefixWord ++ tailWord_861426).sum := by decide
  have hdescent : baseEnd_861426 < baseStart_861426 := by decide
  rcases family_descends (prefixWord ++ tailWord_861426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_861427 : List Nat := [1, 1, 1, 2, 2, 5, 1, 4, 3]
def baseStart_861427 : Nat := 118140960795 + 861427 * 2 ^ 59
def prefixEnd_861427 : Nat := 4983230072969 + 3 ^ 40 * 861427 * 2
def baseEnd_861427 : Nat := 393178755342850130311889

theorem tailTrace_861427 : CollatzResearch.WordTrace tailWord_861427 prefixEnd_861427 393178755342850130311889 := by
  unfold tailWord_861427
  simp only [CollatzResearch.WordTrace]
  refine ⟨31418823850204573863886535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20945882566803049242591023 31418823850204573863886535)
  ·
    refine ⟨47128235775306860795829803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31418823850204573863886535 47128235775306860795829803)
    ·
      refine ⟨70692353662960291193744705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47128235775306860795829803 70692353662960291193744705)
      ·
        refine ⟨53019265247220218395308529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70692353662960291193744705 53019265247220218395308529)
        ·
          refine ⟨39764448935415163796481397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53019265247220218395308529 39764448935415163796481397)
          ·
            refine ⟨3727917087695171605920131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 39764448935415163796481397 3727917087695171605920131)
            ·
              refine ⟨5591875631542757408880197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3727917087695171605920131 5591875631542757408880197)
              ·
                refine ⟨1048476680914267014165037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5591875631542757408880197 1048476680914267014165037)
                ·
                  refine ⟨393178755342850130311889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1048476680914267014165037 393178755342850130311889)
                  ·
                    rfl

theorem cell20_861427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 4, 3].length) (baseStart_861427 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_861427 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_861427 prefixEnd_861427 := by exact prefixLift 861427
  have htrace : WordTrace (prefixWord ++ tailWord_861427) baseStart_861427 baseEnd_861427 := by
    simpa [prefixWord, tailWord_861427, baseEnd_861427] using wordTrace_append hprefix tailTrace_861427
  have hstable : (prefixWord ++ tailWord_861427).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_861427).length < 2 ^ (prefixWord ++ tailWord_861427).sum := by decide
  have hdescent : baseEnd_861427 < baseStart_861427 := by decide
  rcases family_descends (prefixWord ++ tailWord_861427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_861434 : List Nat := [3, 1, 1, 1, 1, 4, 2, 3, 4]
def baseStart_861434 : Nat := 118140960795 + 861434 * 2 ^ 59
def prefixEnd_861434 : Nat := 4983230072969 + 3 ^ 40 * 861434 * 2
def baseEnd_861434 : Nat := 393181950333589217078527

theorem tailTrace_861434 : CollatzResearch.WordTrace tailWord_861434 prefixEnd_861434 393181950333589217078527 := by
  unfold tailWord_861434
  simp only [CollatzResearch.WordTrace]
  refine ⟨7854769790294803514847839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20946052774119476039594237 7854769790294803514847839)
  ·
    refine ⟨11782154685442205272271759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7854769790294803514847839 11782154685442205272271759)
    ·
      refine ⟨17673232028163307908407639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11782154685442205272271759 17673232028163307908407639)
      ·
        refine ⟨26509848042244961862611459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17673232028163307908407639 26509848042244961862611459)
        ·
          refine ⟨39764772063367442793917189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26509848042244961862611459 39764772063367442793917189)
          ·
            refine ⟨7455894761881395523859473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39764772063367442793917189 7455894761881395523859473)
            ·
              refine ⟨5591921071411046642894605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7455894761881395523859473 5591921071411046642894605)
              ·
                refine ⟨2096970401779142491085477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5591921071411046642894605 2096970401779142491085477)
                ·
                  refine ⟨393181950333589217078527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2096970401779142491085477 393181950333589217078527)
                  ·
                    rfl

theorem cell20_861434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 3, 4].length) (baseStart_861434 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_861434 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_861434 prefixEnd_861434 := by exact prefixLift 861434
  have htrace : WordTrace (prefixWord ++ tailWord_861434) baseStart_861434 baseEnd_861434 := by
    simpa [prefixWord, tailWord_861434, baseEnd_861434] using wordTrace_append hprefix tailTrace_861434
  have hstable : (prefixWord ++ tailWord_861434).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_861434).length < 2 ^ (prefixWord ++ tailWord_861434).sum := by decide
  have hdescent : baseEnd_861434 < baseStart_861434 := by decide
  rcases family_descends (prefixWord ++ tailWord_861434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_861444 : List Nat := [2, 3, 2, 2, 2, 1, 2, 3, 3]
def baseStart_861444 : Nat := 118140960795 + 861444 * 2 ^ 59
def prefixEnd_861444 : Nat := 4983230072969 + 3 ^ 40 * 861444 * 2
def baseEnd_861444 : Nat := 393186514606073626745153

theorem tailTrace_861444 : CollatzResearch.WordTrace tailWord_861444 prefixEnd_861444 393186514606073626745153 := by
  unfold tailWord_861444
  simp only [CollatzResearch.WordTrace]
  refine ⟨15709721945571492883627693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20946295927428657178170257 15709721945571492883627693)
  ·
    refine ⟨5891145729589309831360385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15709721945571492883627693 5891145729589309831360385)
    ·
      refine ⟨4418359297191982373520289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5891145729589309831360385 4418359297191982373520289)
      ·
        refine ⟨3313769472893986780140217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4418359297191982373520289 3313769472893986780140217)
        ·
          refine ⟨2485327104670490085105163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3313769472893986780140217 2485327104670490085105163)
          ·
            refine ⟨3727990657005735127657745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2485327104670490085105163 3727990657005735127657745)
            ·
              refine ⟨2795992992754301345743309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3727990657005735127657745 2795992992754301345743309)
              ·
                refine ⟨1048497372282863004653741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2795992992754301345743309 1048497372282863004653741)
                ·
                  refine ⟨393186514606073626745153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1048497372282863004653741 393186514606073626745153)
                  ·
                    rfl

theorem cell20_861444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 2, 3, 3].length) (baseStart_861444 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_861444 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_861444 prefixEnd_861444 := by exact prefixLift 861444
  have htrace : WordTrace (prefixWord ++ tailWord_861444) baseStart_861444 baseEnd_861444 := by
    simpa [prefixWord, tailWord_861444, baseEnd_861444] using wordTrace_append hprefix tailTrace_861444
  have hstable : (prefixWord ++ tailWord_861444).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_861444).length < 2 ^ (prefixWord ++ tailWord_861444).sum := by decide
  have hdescent : baseEnd_861444 < baseStart_861444 := by decide
  rcases family_descends (prefixWord ++ tailWord_861444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_861482 : List Nat := [3, 1, 4, 2, 1, 2, 1, 1, 5]
def baseStart_861482 : Nat := 118140960795 + 861482 * 2 ^ 59
def prefixEnd_861482 : Nat := 4983230072969 + 3 ^ 40 * 861482 * 2
def baseEnd_861482 : Nat := 393203858841514383478331

theorem tailTrace_861482 : CollatzResearch.WordTrace tailWord_861482 prefixEnd_861482 393203858841514383478331 := by
  unfold tailWord_861482
  simp only [CollatzResearch.WordTrace]
  refine ⟨7855207466251329564284675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20947219910003545504759133 7855207466251329564284675)
  ·
    refine ⟨11782811199376994346427013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7855207466251329564284675 11782811199376994346427013)
    ·
      refine ⟨2209277099883186439955065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11782811199376994346427013 2209277099883186439955065)
      ·
        refine ⟨1656957824912389829966299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2209277099883186439955065 1656957824912389829966299)
        ·
          refine ⟨2485436737368584744949449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1656957824912389829966299 2485436737368584744949449)
          ·
            refine ⟨1864077553026438558712087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2485436737368584744949449 1864077553026438558712087)
            ·
              refine ⟨2796116329539657838068131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1864077553026438558712087 2796116329539657838068131)
              ·
                refine ⟨4194174494309486757102197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2796116329539657838068131 4194174494309486757102197)
                ·
                  refine ⟨393203858841514383478331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4194174494309486757102197 393203858841514383478331)
                  ·
                    rfl

theorem cell20_861482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 1, 1, 5].length) (baseStart_861482 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_861482 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_861482 prefixEnd_861482 := by exact prefixLift 861482
  have htrace : WordTrace (prefixWord ++ tailWord_861482) baseStart_861482 baseEnd_861482 := by
    simpa [prefixWord, tailWord_861482, baseEnd_861482] using wordTrace_append hprefix tailTrace_861482
  have hstable : (prefixWord ++ tailWord_861482).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_861482).length < 2 ^ (prefixWord ++ tailWord_861482).sum := by decide
  have hdescent : baseEnd_861482 < baseStart_861482 := by decide
  rcases family_descends (prefixWord ++ tailWord_861482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_861485 : List Nat := [1, 5, 3, 1, 1, 1, 2, 4, 2]
def baseStart_861485 : Nat := 118140960795 + 861485 * 2 ^ 59
def prefixEnd_861485 : Nat := 4983230072969 + 3 ^ 40 * 861485 * 2
def baseEnd_861485 : Nat := 393205228123259706378319

theorem tailTrace_861485 : CollatzResearch.WordTrace tailWord_861485 prefixEnd_861485 393205228123259706378319 := by
  unfold tailWord_861485
  simp only [CollatzResearch.WordTrace]
  refine ⟨31420939283994449769497909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20947292855996299846331939 31420939283994449769497909)
  ·
    refine ⟨2945713057874479665890429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 31420939283994449769497909 2945713057874479665890429)
    ·
      refine ⟨1104642396702929874708911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2945713057874479665890429 1104642396702929874708911)
      ·
        refine ⟨1656963595054394812063367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1104642396702929874708911 1656963595054394812063367)
        ·
          refine ⟨2485445392581592218095051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1656963595054394812063367 2485445392581592218095051)
          ·
            refine ⟨3728168088872388327142577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2485445392581592218095051 3728168088872388327142577)
            ·
              refine ⟨2796126066654291245356933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3728168088872388327142577 2796126066654291245356933)
              ·
                refine ⟨524273637497679608504425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2796126066654291245356933 524273637497679608504425)
                ·
                  refine ⟨393205228123259706378319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 524273637497679608504425 393205228123259706378319)
                  ·
                    rfl

theorem cell20_861485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 2, 4, 2].length) (baseStart_861485 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_861485 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_861485 prefixEnd_861485 := by exact prefixLift 861485
  have htrace : WordTrace (prefixWord ++ tailWord_861485) baseStart_861485 baseEnd_861485 := by
    simpa [prefixWord, tailWord_861485, baseEnd_861485] using wordTrace_append hprefix tailTrace_861485
  have hstable : (prefixWord ++ tailWord_861485).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_861485).length < 2 ^ (prefixWord ++ tailWord_861485).sum := by decide
  have hdescent : baseEnd_861485 < baseStart_861485 := by decide
  rcases family_descends (prefixWord ++ tailWord_861485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_861489 : List Nat := [1, 2, 2, 3, 3, 2, 2, 1, 4]
def baseStart_861489 : Nat := 118140960795 + 861489 * 2 ^ 59
def prefixEnd_861489 : Nat := 4983230072969 + 3 ^ 40 * 861489 * 2
def baseEnd_861489 : Nat := 393207053832253470244969

theorem tailTrace_861489 : CollatzResearch.WordTrace tailWord_861489 prefixEnd_861489 393207053832253470244969 := by
  unfold tailWord_861489
  simp only [CollatzResearch.WordTrace]
  refine ⟨31421085175979958452643521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20947390117319972301762347 31421085175979958452643521)
  ·
    refine ⟨23565813881984968839482641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31421085175979958452643521 23565813881984968839482641)
    ·
      refine ⟨17674360411488726629611981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23565813881984968839482641 17674360411488726629611981)
      ·
        refine ⟨6627885154308272486104493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17674360411488726629611981 6627885154308272486104493)
        ·
          refine ⟨2485456932865602182289185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6627885154308272486104493 2485456932865602182289185)
          ·
            refine ⟨1864092699649201636716889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2485456932865602182289185 1864092699649201636716889)
            ·
              refine ⟨1398069524736901227537667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1864092699649201636716889 1398069524736901227537667)
              ·
                refine ⟨2097104287105351841306501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1398069524736901227537667 2097104287105351841306501)
                ·
                  refine ⟨393207053832253470244969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2097104287105351841306501 393207053832253470244969)
                  ·
                    rfl

theorem cell20_861489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 2, 1, 4].length) (baseStart_861489 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_861489 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_861489 prefixEnd_861489 := by exact prefixLift 861489
  have htrace : WordTrace (prefixWord ++ tailWord_861489) baseStart_861489 baseEnd_861489 := by
    simpa [prefixWord, tailWord_861489, baseEnd_861489] using wordTrace_append hprefix tailTrace_861489
  have hstable : (prefixWord ++ tailWord_861489).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_861489).length < 2 ^ (prefixWord ++ tailWord_861489).sum := by decide
  have hdescent : baseEnd_861489 < baseStart_861489 := by decide
  rcases family_descends (prefixWord ++ tailWord_861489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_861526 : List Nat := [5, 2, 3, 1, 2, 1, 6]
def baseStart_861526 : Nat := 118140960795 + 861526 * 2 ^ 59
def prefixEnd_861526 : Nat := 4983230072969 + 3 ^ 40 * 861526 * 2
def baseEnd_861526 : Nat := 43691549071160642890165

theorem tailTrace_861526 : CollatzResearch.WordTrace tailWord_861526 prefixEnd_861526 43691549071160642890165 := by
  unfold tailWord_861526
  simp only [CollatzResearch.WordTrace]
  refine ⟨1963902167302869610733777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20948289784563942514493621 1963902167302869610733777)
  ·
    refine ⟨1472926625477152208050333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1963902167302869610733777 1472926625477152208050333)
    ·
      refine ⟨552347484553932078018875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1472926625477152208050333 552347484553932078018875)
      ·
        refine ⟨828521226830898117028313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 552347484553932078018875 828521226830898117028313)
        ·
          refine ⟨621390920123173587771235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 828521226830898117028313 621390920123173587771235)
          ·
            refine ⟨932086380184760381656853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 621390920123173587771235 932086380184760381656853)
            ·
              refine ⟨43691549071160642890165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 932086380184760381656853 43691549071160642890165)
              ·
                rfl

theorem cell20_861526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 6].length) (baseStart_861526 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_861526 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_861526 prefixEnd_861526 := by exact prefixLift 861526
  have htrace : WordTrace (prefixWord ++ tailWord_861526) baseStart_861526 baseEnd_861526 := by
    simpa [prefixWord, tailWord_861526, baseEnd_861526] using wordTrace_append hprefix tailTrace_861526
  have hstable : (prefixWord ++ tailWord_861526).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_861526).length < 2 ^ (prefixWord ++ tailWord_861526).sum := by decide
  have hdescent : baseEnd_861526 < baseStart_861526 := by decide
  rcases family_descends (prefixWord ++ tailWord_861526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_861541 : List Nat := [1, 3, 1, 3, 1, 2, 2, 4, 3]
def baseStart_861541 : Nat := 118140960795 + 861541 * 2 ^ 59
def prefixEnd_861541 : Nat := 4983230072969 + 3 ^ 40 * 861541 * 2
def baseEnd_861541 : Nat := 393230788049172400511423

theorem tailTrace_861541 : CollatzResearch.WordTrace tailWord_861541 prefixEnd_861541 393230788049172400511423 := by
  unfold tailWord_861541
  simp only [CollatzResearch.WordTrace]
  refine ⟨31422981771791571333536477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20948654514527714222357651 31422981771791571333536477)
  ·
    refine ⟨11783618164421839250076179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31422981771791571333536477 11783618164421839250076179)
    ·
      refine ⟨17675427246632758875114269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11783618164421839250076179 17675427246632758875114269)
      ·
        refine ⟨6628285217487284578167851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17675427246632758875114269 6628285217487284578167851)
        ·
          refine ⟨9942427826230926867251777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6628285217487284578167851 9942427826230926867251777)
          ·
            refine ⟨7456820869673195150438833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9942427826230926867251777 7456820869673195150438833)
            ·
              refine ⟨5592615652254896362829125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7456820869673195150438833 5592615652254896362829125)
              ·
                refine ⟨1048615434797793068030461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5592615652254896362829125 1048615434797793068030461)
                ·
                  refine ⟨393230788049172400511423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1048615434797793068030461 393230788049172400511423)
                  ·
                    rfl

theorem cell20_861541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 4, 3].length) (baseStart_861541 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_861541 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_861541 prefixEnd_861541 := by exact prefixLift 861541
  have htrace : WordTrace (prefixWord ++ tailWord_861541) baseStart_861541 baseEnd_861541 := by
    simpa [prefixWord, tailWord_861541, baseEnd_861541] using wordTrace_append hprefix tailTrace_861541
  have hstable : (prefixWord ++ tailWord_861541).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_861541).length < 2 ^ (prefixWord ++ tailWord_861541).sum := by decide
  have hdescent : baseEnd_861541 < baseStart_861541 := by decide
  rcases family_descends (prefixWord ++ tailWord_861541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_861544 : List Nat := [2, 1, 4, 2, 3, 2, 1, 1, 4]
def baseStart_861544 : Nat := 118140960795 + 861544 * 2 ^ 59
def prefixEnd_861544 : Nat := 4983230072969 + 3 ^ 40 * 861544 * 2
def baseEnd_861544 : Nat := 393232157330917723411411

theorem tailTrace_861544 : CollatzResearch.WordTrace tailWord_861544 prefixEnd_861544 393232157330917723411411 := by
  unfold tailWord_861544
  simp only [CollatzResearch.WordTrace]
  refine ⟨15711545595390351422947843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20948727460520468563930457 15711545595390351422947843)
  ·
    refine ⟨23567318393085527134421765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15711545595390351422947843 23567318393085527134421765)
    ·
      refine ⟨4418872198703536337704081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23567318393085527134421765 4418872198703536337704081)
      ·
        refine ⟨3314154149027652253278061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4418872198703536337704081 3314154149027652253278061)
        ·
          refine ⟨1242807805885369594979273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3314154149027652253278061 1242807805885369594979273)
          ·
            refine ⟨932105854414027196234455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1242807805885369594979273 932105854414027196234455)
            ·
              refine ⟨1398158781621040794351683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 932105854414027196234455 1398158781621040794351683)
              ·
                refine ⟨2097238172431561191527525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1398158781621040794351683 2097238172431561191527525)
                ·
                  refine ⟨393232157330917723411411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2097238172431561191527525 393232157330917723411411)
                  ·
                    rfl

theorem cell20_861544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 1, 1, 4].length) (baseStart_861544 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_861544 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_861544 prefixEnd_861544 := by exact prefixLift 861544
  have htrace : WordTrace (prefixWord ++ tailWord_861544) baseStart_861544 baseEnd_861544 := by
    simpa [prefixWord, tailWord_861544, baseEnd_861544] using wordTrace_append hprefix tailTrace_861544
  have hstable : (prefixWord ++ tailWord_861544).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_861544).length < 2 ^ (prefixWord ++ tailWord_861544).sum := by decide
  have hdescent : baseEnd_861544 < baseStart_861544 := by decide
  rcases family_descends (prefixWord ++ tailWord_861544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_861599 : List Nat := [1, 1, 2, 5, 1, 4, 2, 2, 2]
def baseStart_861599 : Nat := 118140960795 + 861599 * 2 ^ 59
def prefixEnd_861599 : Nat := 4983230072969 + 3 ^ 40 * 861599 * 2
def baseEnd_861599 : Nat := 393257260829581976577853

theorem tailTrace_861599 : CollatzResearch.WordTrace tailWord_861599 prefixEnd_861599 393257260829581976577853 := by
  unfold tailWord_861599
  simp only [CollatzResearch.WordTrace]
  refine ⟨31425097205581447239147851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20950064803720964826098567 31425097205581447239147851)
  ·
    refine ⟨47137645808372170858721777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31425097205581447239147851 47137645808372170858721777)
    ·
      refine ⟨35353234356279128144041333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47137645808372170858721777 35353234356279128144041333)
      ·
        refine ⟨3314365720901168263503875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 35353234356279128144041333 3314365720901168263503875)
        ·
          refine ⟨4971548581351752395255813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3314365720901168263503875 4971548581351752395255813)
          ·
            refine ⟨932165359003453574110465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4971548581351752395255813 932165359003453574110465)
            ·
              refine ⟨699124019252590180582849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 932165359003453574110465 699124019252590180582849)
              ·
                refine ⟨524343014439442635437137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 699124019252590180582849 524343014439442635437137)
                ·
                  refine ⟨393257260829581976577853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 524343014439442635437137 393257260829581976577853)
                  ·
                    rfl

theorem cell20_861599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 2, 2, 2].length) (baseStart_861599 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_861599 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_861599 prefixEnd_861599 := by exact prefixLift 861599
  have htrace : WordTrace (prefixWord ++ tailWord_861599) baseStart_861599 baseEnd_861599 := by
    simpa [prefixWord, tailWord_861599, baseEnd_861599] using wordTrace_append hprefix tailTrace_861599
  have hstable : (prefixWord ++ tailWord_861599).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_861599).length < 2 ^ (prefixWord ++ tailWord_861599).sum := by decide
  have hdescent : baseEnd_861599 < baseStart_861599 := by decide
  rcases family_descends (prefixWord ++ tailWord_861599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_861603 : List Nat := [1, 1, 1, 4, 1, 3, 3, 4, 2]
def baseStart_861603 : Nat := 118140960795 + 861603 * 2 ^ 59
def prefixEnd_861603 : Nat := 4983230072969 + 3 ^ 40 * 861603 * 2
def baseEnd_861603 : Nat := 393259086538575740444503

theorem tailTrace_861603 : CollatzResearch.WordTrace tailWord_861603 prefixEnd_861603 393259086538575740444503 := by
  unfold tailWord_861603
  simp only [CollatzResearch.WordTrace]
  refine ⟨31425243097566955922293463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20950162065044637281528975 31425243097566955922293463)
  ·
    refine ⟨47137864646350433883440195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31425243097566955922293463 47137864646350433883440195)
    ·
      refine ⟨70706796969525650825160293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47137864646350433883440195 70706796969525650825160293)
      ·
        refine ⟨13257524431786059529717555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70706796969525650825160293 13257524431786059529717555)
        ·
          refine ⟨19886286647679089294576333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13257524431786059529717555 19886286647679089294576333)
          ·
            refine ⟨7457357492879658485466125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19886286647679089294576333 7457357492879658485466125)
            ·
              refine ⟨2796509059829871932049797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7457357492879658485466125 2796509059829871932049797)
              ·
                refine ⟨524345448718100987259337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2796509059829871932049797 524345448718100987259337)
                ·
                  refine ⟨393259086538575740444503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 524345448718100987259337 393259086538575740444503)
                  ·
                    rfl

theorem cell20_861603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 3, 4, 2].length) (baseStart_861603 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_861603 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_861603 prefixEnd_861603 := by exact prefixLift 861603
  have htrace : WordTrace (prefixWord ++ tailWord_861603) baseStart_861603 baseEnd_861603 := by
    simpa [prefixWord, tailWord_861603, baseEnd_861603] using wordTrace_append hprefix tailTrace_861603
  have hstable : (prefixWord ++ tailWord_861603).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_861603).length < 2 ^ (prefixWord ++ tailWord_861603).sum := by decide
  have hdescent : baseEnd_861603 < baseStart_861603 := by decide
  rcases family_descends (prefixWord ++ tailWord_861603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_861617 : List Nat := [1, 2, 2, 4, 1, 1, 1, 5, 3]
def baseStart_861617 : Nat := 118140960795 + 861617 * 2 ^ 59
def prefixEnd_861617 : Nat := 4983230072969 + 3 ^ 40 * 861617 * 2
def baseEnd_861617 : Nat := 393265476520053913977779

theorem tailTrace_861617 : CollatzResearch.WordTrace tailWord_861617 prefixEnd_861617 393265476520053913977779 := by
  unfold tailWord_861617
  simp only [CollatzResearch.WordTrace]
  refine ⟨31425753719516236313303105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20950502479677490875535403 31425753719516236313303105)
  ·
    refine ⟨23569315289637177234977329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31425753719516236313303105 23569315289637177234977329)
    ·
      refine ⟨17676986467227882926232997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23569315289637177234977329 17676986467227882926232997)
      ·
        refine ⟨3314434962605228048668687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17676986467227882926232997 3314434962605228048668687)
        ·
          refine ⟨4971652443907842073003031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3314434962605228048668687 4971652443907842073003031)
          ·
            refine ⟨7457478665861763109504547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4971652443907842073003031 7457478665861763109504547)
            ·
              refine ⟨11186217998792644664256821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7457478665861763109504547 11186217998792644664256821)
              ·
                refine ⟨1048707937386810437274077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11186217998792644664256821 1048707937386810437274077)
                ·
                  refine ⟨393265476520053913977779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1048707937386810437274077 393265476520053913977779)
                  ·
                    rfl

theorem cell20_861617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 5, 3].length) (baseStart_861617 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_861617 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_861617 prefixEnd_861617 := by exact prefixLift 861617
  have htrace : WordTrace (prefixWord ++ tailWord_861617) baseStart_861617 baseEnd_861617 := by
    simpa [prefixWord, tailWord_861617, baseEnd_861617] using wordTrace_append hprefix tailTrace_861617
  have hstable : (prefixWord ++ tailWord_861617).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_861617).length < 2 ^ (prefixWord ++ tailWord_861617).sum := by decide
  have hdescent : baseEnd_861617 < baseStart_861617 := by decide
  rcases family_descends (prefixWord ++ tailWord_861617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_861672 : List Nat := [2, 1, 4, 1, 1, 2, 5, 1, 3]
def baseStart_861672 : Nat := 118140960795 + 861672 * 2 ^ 59
def prefixEnd_861672 : Nat := 4983230072969 + 3 ^ 40 * 861672 * 2
def baseEnd_861672 : Nat := 393290580018718167144221

theorem tailTrace_861672 : CollatzResearch.WordTrace tailWord_861672 prefixEnd_861672 393290580018718167144221 := by
  unfold tailWord_861672
  simp only [CollatzResearch.WordTrace]
  refine ⟨15713879867158490353277635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20951839822877987137703513 15713879867158490353277635)
  ·
    refine ⟨23570819800737735529916453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15713879867158490353277635 23570819800737735529916453)
    ·
      refine ⟨4419528712638325411859335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23570819800737735529916453 4419528712638325411859335)
      ·
        refine ⟨6629293068957488117789003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4419528712638325411859335 6629293068957488117789003)
        ·
          refine ⟨9943939603436232176683505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6629293068957488117789003 9943939603436232176683505)
          ·
            refine ⟨7457954702577174132512629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9943939603436232176683505 7457954702577174132512629)
            ·
              refine ⟨699183253366610074923059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7457954702577174132512629 699183253366610074923059)
              ·
                refine ⟨1048774880049915112384589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 699183253366610074923059 1048774880049915112384589)
                ·
                  refine ⟨393290580018718167144221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1048774880049915112384589 393290580018718167144221)
                  ·
                    rfl

theorem cell20_861672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 5, 1, 3].length) (baseStart_861672 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_861672 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_861672 prefixEnd_861672 := by exact prefixLift 861672
  have htrace : WordTrace (prefixWord ++ tailWord_861672) baseStart_861672 baseEnd_861672 := by
    simpa [prefixWord, tailWord_861672, baseEnd_861672] using wordTrace_append hprefix tailTrace_861672
  have hstable : (prefixWord ++ tailWord_861672).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_861672).length < 2 ^ (prefixWord ++ tailWord_861672).sum := by decide
  have hdescent : baseEnd_861672 < baseStart_861672 := by decide
  rcases family_descends (prefixWord ++ tailWord_861672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_861683 : List Nat := [1, 1, 1, 2, 2, 2, 2, 3, 6]
def baseStart_861683 : Nat := 118140960795 + 861683 * 2 ^ 59
def prefixEnd_861683 : Nat := 4983230072969 + 3 ^ 40 * 861683 * 2
def baseEnd_861683 : Nat := 393295600718451017777509

theorem tailTrace_861683 : CollatzResearch.WordTrace tailWord_861683 prefixEnd_861683 393295600718451017777509 := by
  unfold tailWord_861683
  simp only [CollatzResearch.WordTrace]
  refine ⟨31428160937277129585205703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20952107291518086390137135 31428160937277129585205703)
  ·
    refine ⟨47142241405915694377808555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31428160937277129585205703 47142241405915694377808555)
    ·
      refine ⟨70713362108873541566712833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47142241405915694377808555 70713362108873541566712833)
      ·
        refine ⟨53035021581655156175034625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70713362108873541566712833 53035021581655156175034625)
        ·
          refine ⟨39776266186241367131275969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53035021581655156175034625 39776266186241367131275969)
          ·
            refine ⟨29832199639681025348456977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39776266186241367131275969 29832199639681025348456977)
            ·
              refine ⟨22374149729760769011342733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29832199639681025348456977 22374149729760769011342733)
              ·
                refine ⟨8390306148660288379253525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22374149729760769011342733 8390306148660288379253525)
                ·
                  refine ⟨393295600718451017777509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8390306148660288379253525 393295600718451017777509)
                  ·
                    rfl

theorem cell20_861683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 6].length) (baseStart_861683 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_861683 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_861683 prefixEnd_861683 := by exact prefixLift 861683
  have htrace : WordTrace (prefixWord ++ tailWord_861683) baseStart_861683 baseEnd_861683 := by
    simpa [prefixWord, tailWord_861683, baseEnd_861683] using wordTrace_append hprefix tailTrace_861683
  have hstable : (prefixWord ++ tailWord_861683).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_861683).length < 2 ^ (prefixWord ++ tailWord_861683).sum := by decide
  have hdescent : baseEnd_861683 < baseStart_861683 := by decide
  rcases family_descends (prefixWord ++ tailWord_861683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_861686 : List Nat := [5, 1, 1, 1, 2, 3, 1, 6]
def baseStart_861686 : Nat := 118140960795 + 861686 * 2 ^ 59
def prefixEnd_861686 : Nat := 4983230072969 + 3 ^ 40 * 861686 * 2
def baseEnd_861686 : Nat := 131098990000065446892499

theorem tailTrace_861686 : CollatzResearch.WordTrace tailWord_861686 prefixEnd_861686 131098990000065446892499 := by
  unfold tailWord_861686
  simp only [CollatzResearch.WordTrace]
  refine ⟨1964266897266641318597807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20952180237510840731709941 1964266897266641318597807)
  ·
    refine ⟨2946400345899961977896711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1964266897266641318597807 2946400345899961977896711)
    ·
      refine ⟨4419600518849942966845067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2946400345899961977896711 4419600518849942966845067)
      ·
        refine ⟨6629400778274914450267601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4419600518849942966845067 6629400778274914450267601)
        ·
          refine ⟨4972050583706185837700701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6629400778274914450267601 4972050583706185837700701)
          ·
            refine ⟨1864518968889819689137763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4972050583706185837700701 1864518968889819689137763)
            ·
              refine ⟨2796778453334729533706645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1864518968889819689137763 2796778453334729533706645)
              ·
                refine ⟨131098990000065446892499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2796778453334729533706645 131098990000065446892499)
                ·
                  rfl

theorem cell20_861686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 1, 6].length) (baseStart_861686 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_861686 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_861686 prefixEnd_861686 := by exact prefixLift 861686
  have htrace : WordTrace (prefixWord ++ tailWord_861686) baseStart_861686 baseEnd_861686 := by
    simpa [prefixWord, tailWord_861686, baseEnd_861686] using wordTrace_append hprefix tailTrace_861686
  have hstable : (prefixWord ++ tailWord_861686).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_861686).length < 2 ^ (prefixWord ++ tailWord_861686).sum := by decide
  have hdescent : baseEnd_861686 < baseStart_861686 := by decide
  rcases family_descends (prefixWord ++ tailWord_861686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_861709 : List Nat := [1, 7, 1, 1, 2, 1, 3, 2, 2]
def baseStart_861709 : Nat := 118140960795 + 861709 * 2 ^ 59
def prefixEnd_861709 : Nat := 4983230072969 + 3 ^ 40 * 861709 * 2
def baseEnd_861709 : Nat := 393307467826910482910737

theorem tailTrace_861709 : CollatzResearch.WordTrace tailWord_861709 prefixEnd_861709 393307467826910482910737 := by
  unfold tailWord_861709
  simp only [CollatzResearch.WordTrace]
  refine ⟨31429109235182936025652181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20952739490121957350434787 31429109235182936025652181)
  ·
    refine ⟨736619747699600063101223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 31429109235182936025652181 736619747699600063101223)
    ·
      refine ⟨1104929621549400094651835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 736619747699600063101223 1104929621549400094651835)
      ·
        refine ⟨1657394432324100141977753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1104929621549400094651835 1657394432324100141977753)
        ·
          refine ⟨1243045824243075106483315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1657394432324100141977753 1243045824243075106483315)
          ·
            refine ⟨1864568736364612659724973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1243045824243075106483315 1864568736364612659724973)
            ·
              refine ⟨699213276136729747396865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1864568736364612659724973 699213276136729747396865)
              ·
                refine ⟨524409957102547310547649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 699213276136729747396865 524409957102547310547649)
                ·
                  refine ⟨393307467826910482910737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 524409957102547310547649 393307467826910482910737)
                  ·
                    rfl

theorem cell20_861709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 3, 2, 2].length) (baseStart_861709 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_861709 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_861709 prefixEnd_861709 := by exact prefixLift 861709
  have htrace : WordTrace (prefixWord ++ tailWord_861709) baseStart_861709 baseEnd_861709 := by
    simpa [prefixWord, tailWord_861709, baseEnd_861709] using wordTrace_append hprefix tailTrace_861709
  have hstable : (prefixWord ++ tailWord_861709).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_861709).length < 2 ^ (prefixWord ++ tailWord_861709).sum := by decide
  have hdescent : baseEnd_861709 < baseStart_861709 := by decide
  rcases family_descends (prefixWord ++ tailWord_861709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_861717 : List Nat := [1, 3, 2, 1, 3, 4, 1, 1, 4]
def baseStart_861717 : Nat := 118140960795 + 861717 * 2 ^ 59
def prefixEnd_861717 : Nat := 4983230072969 + 3 ^ 40 * 861717 * 2
def baseEnd_861717 : Nat := 393311119244898010644037

theorem tailTrace_861717 : CollatzResearch.WordTrace tailWord_861717 prefixEnd_861717 393311119244898010644037 := by
  unfold tailWord_861717
  simp only [CollatzResearch.WordTrace]
  refine ⟨31429401019153953391943405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20952934012769302261295603 31429401019153953391943405)
  ·
    refine ⟨11786025382182732521978777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31429401019153953391943405 11786025382182732521978777)
    ·
      refine ⟨8839519036637049391484083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11786025382182732521978777 8839519036637049391484083)
      ·
        refine ⟨13259278554955574087226125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8839519036637049391484083 13259278554955574087226125)
        ·
          refine ⟨4972229458108340282709797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13259278554955574087226125 4972229458108340282709797)
          ·
            refine ⟨932293023395313803008087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4972229458108340282709797 932293023395313803008087)
            ·
              refine ⟨1398439535092970704512131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 932293023395313803008087 1398439535092970704512131)
              ·
                refine ⟨2097659302639456056768197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1398439535092970704512131 2097659302639456056768197)
                ·
                  refine ⟨393311119244898010644037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2097659302639456056768197 393311119244898010644037)
                  ·
                    rfl

theorem cell20_861717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 1, 1, 4].length) (baseStart_861717 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_861717 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_861717 prefixEnd_861717 := by exact prefixLift 861717
  have htrace : WordTrace (prefixWord ++ tailWord_861717) baseStart_861717 baseEnd_861717 := by
    simpa [prefixWord, tailWord_861717, baseEnd_861717] using wordTrace_append hprefix tailTrace_861717
  have hstable : (prefixWord ++ tailWord_861717).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_861717).length < 2 ^ (prefixWord ++ tailWord_861717).sum := by decide
  have hdescent : baseEnd_861717 < baseStart_861717 := by decide
  rcases family_descends (prefixWord ++ tailWord_861717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_861738 : List Nat := [3, 1, 4, 1, 1, 1, 2, 1, 6]
def baseStart_861738 : Nat := 118140960795 + 861738 * 2 ^ 59
def prefixEnd_861738 : Nat := 4983230072969 + 3 ^ 40 * 861738 * 2
def baseEnd_861738 : Nat := 393320704217115270943951

theorem tailTrace_861738 : CollatzResearch.WordTrace tailWord_861738 prefixEnd_861738 393320704217115270943951 := by
  unfold tailWord_861738
  simp only [CollatzResearch.WordTrace]
  refine ⟨7857541738019468494614467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20953444634718582652305245 7857541738019468494614467)
  ·
    refine ⟨11786312607029202741921701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7857541738019468494614467 11786312607029202741921701)
    ·
      refine ⟨2209933613817975514110319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11786312607029202741921701 2209933613817975514110319)
      ·
        refine ⟨3314900420726963271165479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2209933613817975514110319 3314900420726963271165479)
        ·
          refine ⟨4972350631090444906748219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3314900420726963271165479 4972350631090444906748219)
          ·
            refine ⟨7458525946635667360122329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4972350631090444906748219 7458525946635667360122329)
            ·
              refine ⟨5593894459976750520091747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7458525946635667360122329 5593894459976750520091747)
              ·
                refine ⟨8390841689965125780137621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5593894459976750520091747 8390841689965125780137621)
                ·
                  refine ⟨393320704217115270943951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8390841689965125780137621 393320704217115270943951)
                  ·
                    rfl

theorem cell20_861738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 1, 6].length) (baseStart_861738 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_861738 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_861738 prefixEnd_861738 := by exact prefixLift 861738
  have htrace : WordTrace (prefixWord ++ tailWord_861738) baseStart_861738 baseEnd_861738 := by
    simpa [prefixWord, tailWord_861738, baseEnd_861738] using wordTrace_append hprefix tailTrace_861738
  have hstable : (prefixWord ++ tailWord_861738).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_861738).length < 2 ^ (prefixWord ++ tailWord_861738).sum := by decide
  have hdescent : baseEnd_861738 < baseStart_861738 := by decide
  rcases family_descends (prefixWord ++ tailWord_861738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_861772 : List Nat := [2, 2, 1, 3, 1, 3, 4, 2, 2]
def baseStart_861772 : Nat := 118140960795 + 861772 * 2 ^ 59
def prefixEnd_861772 : Nat := 4983230072969 + 3 ^ 40 * 861772 * 2
def baseEnd_861772 : Nat := 393336222743562263810479

theorem tailTrace_861772 : CollatzResearch.WordTrace tailWord_861772 prefixEnd_861772 393336222743562263810479 := by
  unfold tailWord_861772
  simp only [CollatzResearch.WordTrace]
  refine ⟨15715703516977348892597785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20954271355969798523463713 15715703516977348892597785)
  ·
    refine ⟨11786777637733011669448339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15715703516977348892597785 11786777637733011669448339)
    ·
      refine ⟨17680166456599517504172509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11786777637733011669448339 17680166456599517504172509)
      ·
        refine ⟨6630062421224819064064691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17680166456599517504172509 6630062421224819064064691)
        ·
          refine ⟨9945093631837228596097037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6630062421224819064064691 9945093631837228596097037)
          ·
            refine ⟨3729410111938960723536389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9945093631837228596097037 3729410111938960723536389)
            ·
              refine ⟨699264395988555135663073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3729410111938960723536389 699264395988555135663073)
              ·
                refine ⟨524448296991416351747305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 699264395988555135663073 524448296991416351747305)
                ·
                  refine ⟨393336222743562263810479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 524448296991416351747305 393336222743562263810479)
                  ·
                    rfl

theorem cell20_861772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 4, 2, 2].length) (baseStart_861772 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_861772 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_861772 prefixEnd_861772 := by exact prefixLift 861772
  have htrace : WordTrace (prefixWord ++ tailWord_861772) baseStart_861772 baseEnd_861772 := by
    simpa [prefixWord, tailWord_861772, baseEnd_861772] using wordTrace_append hprefix tailTrace_861772
  have hstable : (prefixWord ++ tailWord_861772).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_861772).length < 2 ^ (prefixWord ++ tailWord_861772).sum := by decide
  have hdescent : baseEnd_861772 < baseStart_861772 := by decide
  rcases family_descends (prefixWord ++ tailWord_861772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_861783 : List Nat := [1, 1, 3, 2, 2, 3, 3, 5]
def baseStart_861783 : Nat := 118140960795 + 861783 * 2 ^ 59
def prefixEnd_861783 : Nat := 4983230072969 + 3 ^ 40 * 861783 * 2
def baseEnd_861783 : Nat := 131113747814431704814589

theorem tailTrace_861783 : CollatzResearch.WordTrace tailWord_861783 prefixEnd_861783 131113747814431704814589 := by
  unfold tailWord_861783
  simp only [CollatzResearch.WordTrace]
  refine ⟨31431808236914846663846003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20954538824609897775897335 31431808236914846663846003)
  ·
    refine ⟨47147712355372269995769005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31431808236914846663846003 47147712355372269995769005)
    ·
      refine ⟨17680392133264601248413377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47147712355372269995769005 17680392133264601248413377)
      ·
        refine ⟨13260294099948450936310033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17680392133264601248413377 13260294099948450936310033)
        ·
          refine ⟨9945220574961338202232525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13260294099948450936310033 9945220574961338202232525)
          ·
            refine ⟨3729457715610501825837197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9945220574961338202232525 3729457715610501825837197)
            ·
              refine ⟨1398546643353938184688949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3729457715610501825837197 1398546643353938184688949)
              ·
                refine ⟨131113747814431704814589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1398546643353938184688949 131113747814431704814589)
                ·
                  rfl

theorem cell20_861783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 3, 5].length) (baseStart_861783 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_861783 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_861783 prefixEnd_861783 := by exact prefixLift 861783
  have htrace : WordTrace (prefixWord ++ tailWord_861783) baseStart_861783 baseEnd_861783 := by
    simpa [prefixWord, tailWord_861783, baseEnd_861783] using wordTrace_append hprefix tailTrace_861783
  have hstable : (prefixWord ++ tailWord_861783).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_861783).length < 2 ^ (prefixWord ++ tailWord_861783).sum := by decide
  have hdescent : baseEnd_861783 < baseStart_861783 := by decide
  rcases family_descends (prefixWord ++ tailWord_861783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_861810 : List Nat := [3, 2, 1, 2, 3, 2, 2, 3, 2]
def baseStart_861810 : Nat := 118140960795 + 861810 * 2 ^ 59
def prefixEnd_861810 : Nat := 4983230072969 + 3 ^ 40 * 861810 * 2
def baseEnd_861810 : Nat := 393353566979003020543657

theorem tailTrace_861810 : CollatzResearch.WordTrace tailWord_861810 prefixEnd_861810 393353566979003020543657 := by
  unfold tailWord_861810
  simp only [CollatzResearch.WordTrace]
  refine ⟨7858198251954257568769721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20955195338544686850052589 7858198251954257568769721)
  ·
    refine ⟨5893648688965693176577291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7858198251954257568769721 5893648688965693176577291)
    ·
      refine ⟨8840473033448539764865937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5893648688965693176577291 8840473033448539764865937)
      ·
        refine ⟨6630354775086404823649453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8840473033448539764865937 6630354775086404823649453)
        ·
          refine ⟨2486383040657401808868545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6630354775086404823649453 2486383040657401808868545)
          ·
            refine ⟨1864787280493051356651409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2486383040657401808868545 1864787280493051356651409)
            ·
              refine ⟨1398590460369788517488557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1864787280493051356651409 1398590460369788517488557)
              ·
                refine ⟨524471422638670694058209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1398590460369788517488557 524471422638670694058209)
                ·
                  refine ⟨393353566979003020543657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 524471422638670694058209 393353566979003020543657)
                  ·
                    rfl

theorem cell20_861810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 2, 3, 2].length) (baseStart_861810 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_861810 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_861810 prefixEnd_861810 := by exact prefixLift 861810
  have htrace : WordTrace (prefixWord ++ tailWord_861810) baseStart_861810 baseEnd_861810 := by
    simpa [prefixWord, tailWord_861810, baseEnd_861810] using wordTrace_append hprefix tailTrace_861810
  have hstable : (prefixWord ++ tailWord_861810).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_861810).length < 2 ^ (prefixWord ++ tailWord_861810).sum := by decide
  have hdescent : baseEnd_861810 < baseStart_861810 := by decide
  rcases family_descends (prefixWord ++ tailWord_861810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_861821 : List Nat := [1, 4, 1, 1, 4, 2, 7]
def baseStart_861821 : Nat := 118140960795 + 861821 * 2 ^ 59
def prefixEnd_861821 : Nat := 4983230072969 + 3 ^ 40 * 861821 * 2
def baseEnd_861821 : Nat := 43706509742081763464105

theorem tailTrace_861821 : CollatzResearch.WordTrace tailWord_861821 prefixEnd_861821 43706509742081763464105 := by
  unfold tailWord_861821
  simp only [CollatzResearch.WordTrace]
  refine ⟨31433194210777179153729317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20955462807184786102486211 31433194210777179153729317)
  ·
    refine ⟨5893723914520721091324247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31433194210777179153729317 5893723914520721091324247)
    ·
      refine ⟨8840585871781081636986371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5893723914520721091324247 8840585871781081636986371)
      ·
        refine ⟨13260878807671622455479557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8840585871781081636986371 13260878807671622455479557)
        ·
          refine ⟨2486414776438429210402417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13260878807671622455479557 2486414776438429210402417)
          ·
            refine ⟨1864811082328821907801813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2486414776438429210402417 1864811082328821907801813)
            ·
              refine ⟨43706509742081763464105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1864811082328821907801813 43706509742081763464105)
              ·
                rfl

theorem cell20_861821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 7].length) (baseStart_861821 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_861821 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_861821 prefixEnd_861821 := by exact prefixLift 861821
  have htrace : WordTrace (prefixWord ++ tailWord_861821) baseStart_861821 baseEnd_861821 := by
    simpa [prefixWord, tailWord_861821, baseEnd_861821] using wordTrace_append hprefix tailTrace_861821
  have hstable : (prefixWord ++ tailWord_861821).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_861821).length < 2 ^ (prefixWord ++ tailWord_861821).sum := by decide
  have hdescent : baseEnd_861821 < baseStart_861821 := by decide
  rcases family_descends (prefixWord ++ tailWord_861821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_861831 : List Nat := [1, 1, 4, 2, 1, 3, 2, 4, 2]
def baseStart_861831 : Nat := 118140960795 + 861831 * 2 ^ 59
def prefixEnd_861831 : Nat := 4983230072969 + 3 ^ 40 * 861831 * 2
def baseEnd_861831 : Nat := 393363151951220280843571

theorem tailTrace_861831 : CollatzResearch.WordTrace tailWord_861831 prefixEnd_861831 393363151951220280843571 := by
  unfold tailWord_861831
  simp only [CollatzResearch.WordTrace]
  refine ⟨31433558940740950861593347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20955705960493967241062231 31433558940740950861593347)
  ·
    refine ⟨47150338411111426292390021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31433558940740950861593347 47150338411111426292390021)
    ·
      refine ⟨8840688452083392429823129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47150338411111426292390021 8840688452083392429823129)
      ·
        refine ⟨6630516339062544322367347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8840688452083392429823129 6630516339062544322367347)
        ·
          refine ⟨9945774508593816483551021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6630516339062544322367347 9945774508593816483551021)
          ·
            refine ⟨3729665440722681181331633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9945774508593816483551021 3729665440722681181331633)
            ·
              refine ⟨2797249080542010885998725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3729665440722681181331633 2797249080542010885998725)
              ·
                refine ⟨524484202601627041124761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2797249080542010885998725 524484202601627041124761)
                ·
                  refine ⟨393363151951220280843571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 524484202601627041124761 393363151951220280843571)
                  ·
                    rfl

theorem cell20_861831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 2, 4, 2].length) (baseStart_861831 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_861831 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_861831 prefixEnd_861831 := by exact prefixLift 861831
  have htrace : WordTrace (prefixWord ++ tailWord_861831) baseStart_861831 baseEnd_861831 := by
    simpa [prefixWord, tailWord_861831, baseEnd_861831] using wordTrace_append hprefix tailTrace_861831
  have hstable : (prefixWord ++ tailWord_861831).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_861831).length < 2 ^ (prefixWord ++ tailWord_861831).sum := by decide
  have hdescent : baseEnd_861831 < baseStart_861831 := by decide
  rcases family_descends (prefixWord ++ tailWord_861831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_861900 : List Nat := [2, 2, 1, 5, 2, 1, 1, 3, 3]
def baseStart_861900 : Nat := 118140960795 + 861900 * 2 ^ 59
def prefixEnd_861900 : Nat := 4983230072969 + 3 ^ 40 * 861900 * 2
def baseEnd_861900 : Nat := 393394645431362707543289

theorem tailTrace_861900 : CollatzResearch.WordTrace tailWord_861900 prefixEnd_861900 393394645431362707543289 := by
  unfold tailWord_861900
  simp only [CollatzResearch.WordTrace]
  refine ⟨15718037788745487822927577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20957383718327317097236769 15718037788745487822927577)
  ·
    refine ⟨11788528341559115867195683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15718037788745487822927577 11788528341559115867195683)
    ·
      refine ⟨17682792512338673800793525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11788528341559115867195683 17682792512338673800793525)
      ·
        refine ⟨1657761798031750668824393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 17682792512338673800793525 1657761798031750668824393)
        ·
          refine ⟨1243321348523813001618295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1657761798031750668824393 1243321348523813001618295)
          ·
            refine ⟨1864982022785719502427443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1243321348523813001618295 1864982022785719502427443)
            ·
              refine ⟨2797473034178579253641165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1864982022785719502427443 2797473034178579253641165)
              ·
                refine ⟨1049052387816967220115437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2797473034178579253641165 1049052387816967220115437)
                ·
                  refine ⟨393394645431362707543289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1049052387816967220115437 393394645431362707543289)
                  ·
                    rfl

theorem cell20_861900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 1, 3, 3].length) (baseStart_861900 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_861900 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_861900 prefixEnd_861900 := by exact prefixLift 861900
  have htrace : WordTrace (prefixWord ++ tailWord_861900) baseStart_861900 baseEnd_861900 := by
    simpa [prefixWord, tailWord_861900, baseEnd_861900] using wordTrace_append hprefix tailTrace_861900
  have hstable : (prefixWord ++ tailWord_861900).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_861900).length < 2 ^ (prefixWord ++ tailWord_861900).sum := by decide
  have hdescent : baseEnd_861900 < baseStart_861900 := by decide
  rcases family_descends (prefixWord ++ tailWord_861900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_861911 : List Nat := [1, 1, 3, 2, 1, 3, 2, 1, 6]
def baseStart_861911 : Nat := 118140960795 + 861911 * 2 ^ 59
def prefixEnd_861911 : Nat := 4983230072969 + 3 ^ 40 * 861911 * 2
def baseEnd_861911 : Nat := 393399666131095558176577

theorem tailTrace_861911 : CollatzResearch.WordTrace tailWord_861911 prefixEnd_861911 393399666131095558176577 := by
  unfold tailWord_861911
  simp only [CollatzResearch.WordTrace]
  refine ⟨31436476780451124524505587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20957651186967416349670391 31436476780451124524505587)
  ·
    refine ⟨47154715170676686786758381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31436476780451124524505587 47154715170676686786758381)
    ·
      refine ⟨17683018189003757545034393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47154715170676686786758381 17683018189003757545034393)
      ·
        refine ⟨13262263641752818158775795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17683018189003757545034393 13262263641752818158775795)
        ·
          refine ⟨19893395462629227238163693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13262263641752818158775795 19893395462629227238163693)
          ·
            refine ⟨7460023298485960214311385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19893395462629227238163693 7460023298485960214311385)
            ·
              refine ⟨5595017473864470160733539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7460023298485960214311385 5595017473864470160733539)
              ·
                refine ⟨8392526210796705241100309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5595017473864470160733539 8392526210796705241100309)
                ·
                  refine ⟨393399666131095558176577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8392526210796705241100309 393399666131095558176577)
                  ·
                    rfl

theorem cell20_861911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 1, 6].length) (baseStart_861911 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_861911 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_861911 prefixEnd_861911 := by exact prefixLift 861911
  have htrace : WordTrace (prefixWord ++ tailWord_861911) baseStart_861911 baseEnd_861911 := by
    simpa [prefixWord, tailWord_861911, baseEnd_861911] using wordTrace_append hprefix tailTrace_861911
  have hstable : (prefixWord ++ tailWord_861911).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_861911).length < 2 ^ (prefixWord ++ tailWord_861911).sum := by decide
  have hdescent : baseEnd_861911 < baseStart_861911 := by decide
  rcases family_descends (prefixWord ++ tailWord_861911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_861980 : List Nat := [2, 2, 3, 1, 1, 2, 2, 2, 5]
def baseStart_861980 : Nat := 118140960795 + 861980 * 2 ^ 59
def prefixEnd_861980 : Nat := 4983230072969 + 3 ^ 40 * 861980 * 2
def baseEnd_861980 : Nat := 393431159611237984876295

theorem tailTrace_861980 : CollatzResearch.WordTrace tailWord_861980 prefixEnd_861980 393431159611237984876295 := by
  unfold tailWord_861980
  simp only [CollatzResearch.WordTrace]
  refine ⟨15719496708600574654383697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20959328944800766205844929 15719496708600574654383697)
  ·
    refine ⟨11789622531450430990787773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15719496708600574654383697 11789622531450430990787773)
    ·
      refine ⟨4421108449293911621545415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11789622531450430990787773 4421108449293911621545415)
      ·
        refine ⟨6631662673940867432318123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4421108449293911621545415 6631662673940867432318123)
        ·
          refine ⟨9947494010911301148477185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6631662673940867432318123 9947494010911301148477185)
          ·
            refine ⟨7460620508183475861357889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9947494010911301148477185 7460620508183475861357889)
            ·
              refine ⟨5595465381137606896018417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7460620508183475861357889 5595465381137606896018417)
              ·
                refine ⟨4196599035853205172013813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5595465381137606896018417 4196599035853205172013813)
                ·
                  refine ⟨393431159611237984876295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4196599035853205172013813 393431159611237984876295)
                  ·
                    rfl

theorem cell20_861980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 2, 5].length) (baseStart_861980 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_861980 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_861980 prefixEnd_861980 := by exact prefixLift 861980
  have htrace : WordTrace (prefixWord ++ tailWord_861980) baseStart_861980 baseEnd_861980 := by
    simpa [prefixWord, tailWord_861980, baseEnd_861980] using wordTrace_append hprefix tailTrace_861980
  have hstable : (prefixWord ++ tailWord_861980).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_861980).length < 2 ^ (prefixWord ++ tailWord_861980).sum := by decide
  have hdescent : baseEnd_861980 < baseStart_861980 := by decide
  rcases family_descends (prefixWord ++ tailWord_861980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_861983 : List Nat := [1, 1, 2, 4, 2, 1, 4, 3, 2]
def baseStart_861983 : Nat := 118140960795 + 861983 * 2 ^ 59
def prefixEnd_861983 : Nat := 4983230072969 + 3 ^ 40 * 861983 * 2
def baseEnd_861983 : Nat := 393432528892983307776283

theorem tailTrace_861983 : CollatzResearch.WordTrace tailWord_861983 prefixEnd_861983 393432528892983307776283 := by
  unfold tailWord_861983
  simp only [CollatzResearch.WordTrace]
  refine ⟨31439102836190280821126603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20959401890793520547417735 31439102836190280821126603)
  ·
    refine ⟨47158654254285421231689905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31439102836190280821126603 47158654254285421231689905)
    ·
      refine ⟨35368990690714065923767429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47158654254285421231689905 35368990690714065923767429)
      ·
        refine ⟨6631685754508887360706393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35368990690714065923767429 6631685754508887360706393)
        ·
          refine ⟨4973764315881665520529795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6631685754508887360706393 4973764315881665520529795)
          ·
            refine ⟨7460646473822498280794693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4973764315881665520529795 7460646473822498280794693)
            ·
              refine ⟨1398871213841718427649005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7460646473822498280794693 1398871213841718427649005)
              ·
                refine ⟨524576705190644410368377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1398871213841718427649005 524576705190644410368377)
                ·
                  refine ⟨393432528892983307776283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 524576705190644410368377 393432528892983307776283)
                  ·
                    rfl

theorem cell20_861983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 4, 3, 2].length) (baseStart_861983 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_861983 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_861983 prefixEnd_861983 := by exact prefixLift 861983
  have htrace : WordTrace (prefixWord ++ tailWord_861983) baseStart_861983 baseEnd_861983 := by
    simpa [prefixWord, tailWord_861983, baseEnd_861983] using wordTrace_append hprefix tailTrace_861983
  have hstable : (prefixWord ++ tailWord_861983).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_861983).length < 2 ^ (prefixWord ++ tailWord_861983).sum := by decide
  have hdescent : baseEnd_861983 < baseStart_861983 := by decide
  rcases family_descends (prefixWord ++ tailWord_861983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_862025 : List Nat := [1, 2, 1, 1, 2, 4, 1, 4, 4]
def baseStart_862025 : Nat := 118140960795 + 862025 * 2 ^ 59
def prefixEnd_862025 : Nat := 4983230072969 + 3 ^ 40 * 862025 * 2
def baseEnd_862025 : Nat := 393451698837417828376111

theorem tailTrace_862025 : CollatzResearch.WordTrace tailWord_862025 prefixEnd_862025 393451698837417828376111 := by
  unfold tailWord_862025
  simp only [CollatzResearch.WordTrace]
  refine ⟨31440634702038121994155529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20960423134692081329437019 31440634702038121994155529)
  ·
    refine ⟨23580476026528591495616647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31440634702038121994155529 23580476026528591495616647)
    ·
      refine ⟨35370714039792887243424971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23580476026528591495616647 35370714039792887243424971)
      ·
        refine ⟨53056071059689330865137457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35370714039792887243424971 53056071059689330865137457)
        ·
          refine ⟨39792053294766998148853093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53056071059689330865137457 39792053294766998148853093)
          ·
            refine ⟨7461009992768812152909955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39792053294766998148853093 7461009992768812152909955)
            ·
              refine ⟨11191514989153218229364933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7461009992768812152909955 11191514989153218229364933)
              ·
                refine ⟨2098409060466228418005925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11191514989153218229364933 2098409060466228418005925)
                ·
                  refine ⟨393451698837417828376111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2098409060466228418005925 393451698837417828376111)
                  ·
                    rfl

theorem cell20_862025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 4, 4].length) (baseStart_862025 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_862025 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_862025 prefixEnd_862025 := by exact prefixLift 862025
  have htrace : WordTrace (prefixWord ++ tailWord_862025) baseStart_862025 baseEnd_862025 := by
    simpa [prefixWord, tailWord_862025, baseEnd_862025] using wordTrace_append hprefix tailTrace_862025
  have hstable : (prefixWord ++ tailWord_862025).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_862025).length < 2 ^ (prefixWord ++ tailWord_862025).sum := by decide
  have hdescent : baseEnd_862025 < baseStart_862025 := by decide
  rcases family_descends (prefixWord ++ tailWord_862025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_862056 : List Nat := [2, 1, 4, 2, 1, 1, 1, 3, 5]
def baseStart_862056 : Nat := 118140960795 + 862056 * 2 ^ 59
def prefixEnd_862056 : Nat := 4983230072969 + 3 ^ 40 * 862056 * 2
def baseEnd_862056 : Nat := 393465848082119498342651

theorem tailTrace_862056 : CollatzResearch.WordTrace tailWord_862056 prefixEnd_862056 393465848082119498342651 := by
  unfold tailWord_862056
  simp only [CollatzResearch.WordTrace]
  refine ⟨15720882682462907144267011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20961176909950542859022681 15720882682462907144267011)
  ·
    refine ⟨23581324023694360716400517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15720882682462907144267011 23581324023694360716400517)
    ·
      refine ⟨4421498254442692634325097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23581324023694360716400517 4421498254442692634325097)
      ·
        refine ⟨3316123690832019475743823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4421498254442692634325097 3316123690832019475743823)
        ·
          refine ⟨4974185536248029213615735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3316123690832019475743823 4974185536248029213615735)
          ·
            refine ⟨7461278304372043820423603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4974185536248029213615735 7461278304372043820423603)
            ·
              refine ⟨11191917456558065730635405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7461278304372043820423603 11191917456558065730635405)
              ·
                refine ⟨4196969046209274648988277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11191917456558065730635405 4196969046209274648988277)
                ·
                  refine ⟨393465848082119498342651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4196969046209274648988277 393465848082119498342651)
                  ·
                    rfl

theorem cell20_862056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 3, 5].length) (baseStart_862056 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_862056 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_862056 prefixEnd_862056 := by exact prefixLift 862056
  have htrace : WordTrace (prefixWord ++ tailWord_862056) baseStart_862056 baseEnd_862056 := by
    simpa [prefixWord, tailWord_862056, baseEnd_862056] using wordTrace_append hprefix tailTrace_862056
  have hstable : (prefixWord ++ tailWord_862056).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_862056).length < 2 ^ (prefixWord ++ tailWord_862056).sum := by decide
  have hdescent : baseEnd_862056 < baseStart_862056 := by decide
  rcases family_descends (prefixWord ++ tailWord_862056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_862104 : List Nat := [2, 1, 2, 6, 2, 7]
def baseStart_862104 : Nat := 118140960795 + 862104 * 2 ^ 59
def prefixEnd_862104 : Nat := 4983230072969 + 3 ^ 40 * 862104 * 2
def baseEnd_862104 : Nat := 14573620614446098694165

theorem tailTrace_862104 : CollatzResearch.WordTrace tailWord_862104 prefixEnd_862104 14573620614446098694165 := by
  unfold tailWord_862104
  simp only [CollatzResearch.WordTrace]
  refine ⟨15721758034375959243140683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20962344045834612324187577 15721758034375959243140683)
  ·
    refine ⟨23582637051563938864711025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15721758034375959243140683 23582637051563938864711025)
    ·
      refine ⟨17686977788672954148533269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23582637051563938864711025 17686977788672954148533269)
      ·
        refine ⟨829077083844044725712497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 17686977788672954148533269 829077083844044725712497)
        ·
          refine ⟨621807812883033544284373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 829077083844044725712497 621807812883033544284373)
          ·
            refine ⟨14573620614446098694165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 621807812883033544284373 14573620614446098694165)
            ·
              rfl

theorem cell20_862104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 7].length) (baseStart_862104 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_862104 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_862104 prefixEnd_862104 := by exact prefixLift 862104
  have htrace : WordTrace (prefixWord ++ tailWord_862104) baseStart_862104 baseEnd_862104 := by
    simpa [prefixWord, tailWord_862104, baseEnd_862104] using wordTrace_append hprefix tailTrace_862104
  have hstable : (prefixWord ++ tailWord_862104).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_862104).length < 2 ^ (prefixWord ++ tailWord_862104).sum := by decide
  have hdescent : baseEnd_862104 < baseStart_862104 := by decide
  rcases family_descends (prefixWord ++ tailWord_862104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_862114 : List Nat := [3, 3, 1, 2, 3, 1, 1, 4, 2]
def baseStart_862114 : Nat := 118140960795 + 862114 * 2 ^ 59
def prefixEnd_862114 : Nat := 4983230072969 + 3 ^ 40 * 862114 * 2
def baseEnd_862114 : Nat := 393492320862529074409081

theorem tailTrace_862114 : CollatzResearch.WordTrace tailWord_862114 prefixEnd_862114 393492320862529074409081 := by
  unfold tailWord_862114
  simp only [CollatzResearch.WordTrace]
  refine ⟨7860970199678922548536349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20962587199143793462763597 7860970199678922548536349)
  ·
    refine ⟨2947863824879595955701131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7860970199678922548536349 2947863824879595955701131)
    ·
      refine ⟨4421795737319393933551697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2947863824879595955701131 4421795737319393933551697)
      ·
        refine ⟨3316346802989545450163773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4421795737319393933551697 3316346802989545450163773)
        ·
          refine ⟨1243630051121079543811415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3316346802989545450163773 1243630051121079543811415)
          ·
            refine ⟨1865445076681619315717123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1243630051121079543811415 1865445076681619315717123)
            ·
              refine ⟨2798167615022428973575685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1865445076681619315717123 2798167615022428973575685)
              ·
                refine ⟨524656427816705432545441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2798167615022428973575685 524656427816705432545441)
                ·
                  refine ⟨393492320862529074409081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 524656427816705432545441 393492320862529074409081)
                  ·
                    rfl

theorem cell20_862114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 1, 4, 2].length) (baseStart_862114 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_862114 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_862114 prefixEnd_862114 := by exact prefixLift 862114
  have htrace : WordTrace (prefixWord ++ tailWord_862114) baseStart_862114 baseEnd_862114 := by
    simpa [prefixWord, tailWord_862114, baseEnd_862114] using wordTrace_append hprefix tailTrace_862114
  have hstable : (prefixWord ++ tailWord_862114).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_862114).length < 2 ^ (prefixWord ++ tailWord_862114).sum := by decide
  have hdescent : baseEnd_862114 < baseStart_862114 := by decide
  rcases family_descends (prefixWord ++ tailWord_862114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_862142 : List Nat := [4, 2, 1, 1, 1, 4, 3, 4]
def baseStart_862142 : Nat := 118140960795 + 862142 * 2 ^ 59
def prefixEnd_862142 : Nat := 4983230072969 + 3 ^ 40 * 862142 * 2
def baseEnd_862142 : Nat := 131168366941828473825211

theorem tailTrace_862142 : CollatzResearch.WordTrace tailWord_862142 prefixEnd_862142 131168366941828473825211 := by
  unfold tailWord_862142
  simp only [CollatzResearch.WordTrace]
  refine ⟨3930612755326781372020585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20963268028409500650776453 3930612755326781372020585)
  ·
    refine ⟨2947959566495086029015439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3930612755326781372020585 2947959566495086029015439)
    ·
      refine ⟨4421939349742629043523159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2947959566495086029015439 4421939349742629043523159)
      ·
        refine ⟨6632909024613943565284739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4421939349742629043523159 6632909024613943565284739)
        ·
          refine ⟨9949363536920915347927109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6632909024613943565284739 9949363536920915347927109)
          ·
            refine ⟨1865505663172671627736333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9949363536920915347927109 1865505663172671627736333)
            ·
              refine ⟨699564623689751860401125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1865505663172671627736333 699564623689751860401125)
              ·
                refine ⟨131168366941828473825211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 699564623689751860401125 131168366941828473825211)
                ·
                  rfl

theorem cell20_862142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 3, 4].length) (baseStart_862142 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_862142 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_862142 prefixEnd_862142 := by exact prefixLift 862142
  have htrace : WordTrace (prefixWord ++ tailWord_862142) baseStart_862142 baseEnd_862142 := by
    simpa [prefixWord, tailWord_862142, baseEnd_862142] using wordTrace_append hprefix tailTrace_862142
  have hstable : (prefixWord ++ tailWord_862142).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_862142).length < 2 ^ (prefixWord ++ tailWord_862142).sum := by decide
  have hdescent : baseEnd_862142 < baseStart_862142 := by decide
  rcases family_descends (prefixWord ++ tailWord_862142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_862153 : List Nat := [1, 2, 1, 1, 2, 1, 2, 3, 7]
def baseStart_862153 : Nat := 118140960795 + 862153 * 2 ^ 59
def prefixEnd_862153 : Nat := 4983230072969 + 3 ^ 40 * 862153 * 2
def baseEnd_862153 : Nat := 393510121525218272108921

theorem tailTrace_862153 : CollatzResearch.WordTrace tailWord_862153 prefixEnd_862153 393510121525218272108921 := by
  unfold tailWord_862153
  simp only [CollatzResearch.WordTrace]
  refine ⟨31445303245574399854815113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20963535497049599903210075 31445303245574399854815113)
  ·
    refine ⟨23583977434180799891111335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31445303245574399854815113 23583977434180799891111335)
    ·
      refine ⟨35375966151271199836667003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23583977434180799891111335 35375966151271199836667003)
      ·
        refine ⟨53063949226906799755000505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35375966151271199836667003 53063949226906799755000505)
        ·
          refine ⟨39797961920180099816250379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53063949226906799755000505 39797961920180099816250379)
          ·
            refine ⟨59696942880270149724375569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39797961920180099816250379 59696942880270149724375569)
            ·
              refine ⟨44772707160202612293281677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59696942880270149724375569 44772707160202612293281677)
              ·
                refine ⟨16789765185075979609980629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44772707160202612293281677 16789765185075979609980629)
                ·
                  refine ⟨393510121525218272108921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16789765185075979609980629 393510121525218272108921)
                  ·
                    rfl

theorem cell20_862153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 3, 7].length) (baseStart_862153 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_862153 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_862153 prefixEnd_862153 := by exact prefixLift 862153
  have htrace : WordTrace (prefixWord ++ tailWord_862153) baseStart_862153 baseEnd_862153 := by
    simpa [prefixWord, tailWord_862153, baseEnd_862153] using wordTrace_append hprefix tailTrace_862153
  have hstable : (prefixWord ++ tailWord_862153).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_862153).length < 2 ^ (prefixWord ++ tailWord_862153).sum := by decide
  have hdescent : baseEnd_862153 < baseStart_862153 := by decide
  rcases family_descends (prefixWord ++ tailWord_862153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_862166 : List Nat := [5, 2, 1, 1, 3, 1, 1, 1, 5]
def baseStart_862166 : Nat := 118140960795 + 862166 * 2 ^ 59
def prefixEnd_862166 : Nat := 4983230072969 + 3 ^ 40 * 862166 * 2
def baseEnd_862166 : Nat := 393516055079448004675535

theorem tailTrace_862166 : CollatzResearch.WordTrace tailWord_862166 prefixEnd_862166 393516055079448004675535 := by
  unfold tailWord_862166
  simp only [CollatzResearch.WordTrace]
  refine ⟨1965361087157956442189897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20963851596351535383358901 1965361087157956442189897)
  ·
    refine ⟨1474020815368467331642423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1965361087157956442189897 1474020815368467331642423)
    ·
      refine ⟨2211031223052700997463635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1474020815368467331642423 2211031223052700997463635)
      ·
        refine ⟨3316546834579051496195453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2211031223052700997463635 3316546834579051496195453)
        ·
          refine ⟨1243705062967144311073295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3316546834579051496195453 1243705062967144311073295)
          ·
            refine ⟨1865557594450716466609943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1243705062967144311073295 1865557594450716466609943)
            ·
              refine ⟨2798336391676074699914915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1865557594450716466609943 2798336391676074699914915)
              ·
                refine ⟨4197504587514112049872373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2798336391676074699914915 4197504587514112049872373)
                ·
                  refine ⟨393516055079448004675535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4197504587514112049872373 393516055079448004675535)
                  ·
                    rfl

theorem cell20_862166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 1, 1, 5].length) (baseStart_862166 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_862166 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_862166 prefixEnd_862166 := by exact prefixLift 862166
  have htrace : WordTrace (prefixWord ++ tailWord_862166) baseStart_862166 baseEnd_862166 := by
    simpa [prefixWord, tailWord_862166, baseEnd_862166] using wordTrace_append hprefix tailTrace_862166
  have hstable : (prefixWord ++ tailWord_862166).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_862166).length < 2 ^ (prefixWord ++ tailWord_862166).sum := by decide
  have hdescent : baseEnd_862166 < baseStart_862166 := by decide
  rcases family_descends (prefixWord ++ tailWord_862166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_862173 : List Nat := [1, 4, 3, 1, 3, 1, 2, 1, 4]
def baseStart_862173 : Nat := 118140960795 + 862173 * 2 ^ 59
def prefixEnd_862173 : Nat := 4983230072969 + 3 ^ 40 * 862173 * 2
def baseEnd_862173 : Nat := 393519250070187091442173

theorem tailTrace_862173 : CollatzResearch.WordTrace tailWord_862173 prefixEnd_862173 393519250070187091442173 := by
  unfold tailWord_862173
  simp only [CollatzResearch.WordTrace]
  refine ⟨31446032705501943270543173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20964021803667962180362115 31446032705501943270543173)
  ·
    refine ⟨5896131132281614363226845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31446032705501943270543173 5896131132281614363226845)
    ·
      refine ⟨2211049174605605386210067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5896131132281614363226845 2211049174605605386210067)
      ·
        refine ⟨3316573761908408079315101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2211049174605605386210067 3316573761908408079315101)
        ·
          refine ⟨1243715160715653029743163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3316573761908408079315101 1243715160715653029743163)
          ·
            refine ⟨1865572741073479544614745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1243715160715653029743163 1865572741073479544614745)
            ·
              refine ⟨1399179555805109658461059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1865572741073479544614745 1399179555805109658461059)
              ·
                refine ⟨2098769333707664487691589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1399179555805109658461059 2098769333707664487691589)
                ·
                  refine ⟨393519250070187091442173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2098769333707664487691589 393519250070187091442173)
                  ·
                    rfl

theorem cell20_862173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 2, 1, 4].length) (baseStart_862173 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_862173 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_862173 prefixEnd_862173 := by exact prefixLift 862173
  have htrace : WordTrace (prefixWord ++ tailWord_862173) baseStart_862173 baseEnd_862173 := by
    simpa [prefixWord, tailWord_862173, baseEnd_862173] using wordTrace_append hprefix tailTrace_862173
  have hstable : (prefixWord ++ tailWord_862173).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_862173).length < 2 ^ (prefixWord ++ tailWord_862173).sum := by decide
  have hdescent : baseEnd_862173 < baseStart_862173 := by decide
  rcases family_descends (prefixWord ++ tailWord_862173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_862177 : List Nat := [1, 2, 3, 1, 2, 1, 3, 3, 4]
def baseStart_862177 : Nat := 118140960795 + 862177 * 2 ^ 59
def prefixEnd_862177 : Nat := 4983230072969 + 3 ^ 40 * 862177 * 2
def baseEnd_862177 : Nat := 393521075779180855308823

theorem tailTrace_862177 : CollatzResearch.WordTrace tailWord_862177 prefixEnd_862177 393521075779180855308823 := by
  unfold tailWord_862177
  simp only [CollatzResearch.WordTrace]
  refine ⟨31446178597487451953688785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20964119064991634635792523 31446178597487451953688785)
  ·
    refine ⟨23584633948115588965266589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31446178597487451953688785 23584633948115588965266589)
    ·
      refine ⟨8844237730543345861974971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23584633948115588965266589 8844237730543345861974971)
      ·
        refine ⟨13266356595815018792962457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8844237730543345861974971 13266356595815018792962457)
        ·
          refine ⟨9949767446861264094721843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13266356595815018792962457 9949767446861264094721843)
          ·
            refine ⟨14924651170291896142082765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9949767446861264094721843 14924651170291896142082765)
            ·
              refine ⟨5596744188859461053281037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14924651170291896142082765 5596744188859461053281037)
              ·
                refine ⟨2098779070822297894980389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5596744188859461053281037 2098779070822297894980389)
                ·
                  refine ⟨393521075779180855308823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2098779070822297894980389 393521075779180855308823)
                  ·
                    rfl

theorem cell20_862177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 3, 4].length) (baseStart_862177 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_862177 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_862177 prefixEnd_862177 := by exact prefixLift 862177
  have htrace : WordTrace (prefixWord ++ tailWord_862177) baseStart_862177 baseEnd_862177 := by
    simpa [prefixWord, tailWord_862177, baseEnd_862177] using wordTrace_append hprefix tailTrace_862177
  have hstable : (prefixWord ++ tailWord_862177).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_862177).length < 2 ^ (prefixWord ++ tailWord_862177).sum := by decide
  have hdescent : baseEnd_862177 < baseStart_862177 := by decide
  rcases family_descends (prefixWord ++ tailWord_862177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_862184 : List Nat := [2, 1, 4, 1, 1, 1, 1, 9]
def baseStart_862184 : Nat := 118140960795 + 862184 * 2 ^ 59
def prefixEnd_862184 : Nat := 4983230072969 + 3 ^ 40 * 862184 * 2
def baseEnd_862184 : Nat := 131174756923306647358487

theorem tailTrace_862184 : CollatzResearch.WordTrace tailWord_862184 prefixEnd_862184 131174756923306647358487 := by
  unfold tailWord_862184
  simp only [CollatzResearch.WordTrace]
  refine ⟨15723216954231046074596803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20964289272308061432795737 15723216954231046074596803)
  ·
    refine ⟨23584825431346569111895205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15723216954231046074596803 23584825431346569111895205)
    ·
      refine ⟨4422154768377481708480351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23584825431346569111895205 4422154768377481708480351)
      ·
        refine ⟨6633232152566222562720527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4422154768377481708480351 6633232152566222562720527)
        ·
          refine ⟨9949848228849333844080791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6633232152566222562720527 9949848228849333844080791)
          ·
            refine ⟨14924772343274000766121187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9949848228849333844080791 14924772343274000766121187)
            ·
              refine ⟨22387158514911001149181781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14924772343274000766121187 22387158514911001149181781)
              ·
                refine ⟨131174756923306647358487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 22387158514911001149181781 131174756923306647358487)
                ·
                  rfl

theorem cell20_862184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 9].length) (baseStart_862184 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_862184 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_862184 prefixEnd_862184 := by exact prefixLift 862184
  have htrace : WordTrace (prefixWord ++ tailWord_862184) baseStart_862184 baseEnd_862184 := by
    simpa [prefixWord, tailWord_862184, baseEnd_862184] using wordTrace_append hprefix tailTrace_862184
  have hstable : (prefixWord ++ tailWord_862184).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_862184).length < 2 ^ (prefixWord ++ tailWord_862184).sum := by decide
  have hdescent : baseEnd_862184 < baseStart_862184 := by decide
  rcases family_descends (prefixWord ++ tailWord_862184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_862201 : List Nat := [1, 2, 1, 3, 1, 4, 4, 4]
def baseStart_862201 : Nat := 118140960795 + 862201 * 2 ^ 59
def prefixEnd_862201 : Nat := 4983230072969 + 3 ^ 40 * 862201 * 2
def baseEnd_862201 : Nat := 131177343344381146169575

theorem tailTrace_862201 : CollatzResearch.WordTrace tailWord_862201 prefixEnd_862201 131177343344381146169575 := by
  unfold tailWord_862201
  simp only [CollatzResearch.WordTrace]
  refine ⟨31447053949400504052562457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20964702632933669368374971 31447053949400504052562457)
  ·
    refine ⟨23585290462050378039421843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31447053949400504052562457 23585290462050378039421843)
    ·
      refine ⟨35377935693075567059132765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23585290462050378039421843 35377935693075567059132765)
      ·
        refine ⟨13266725884903337647174787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35377935693075567059132765 13266725884903337647174787)
        ·
          refine ⟨19900088827355006470762181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13266725884903337647174787 19900088827355006470762181)
          ·
            refine ⟨3731266655129063713267909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19900088827355006470762181 3731266655129063713267909)
            ·
              refine ⟨699612497836699446237733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3731266655129063713267909 699612497836699446237733)
              ·
                refine ⟨131177343344381146169575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 699612497836699446237733 131177343344381146169575)
                ·
                  rfl

theorem cell20_862201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 4, 4].length) (baseStart_862201 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_862201 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_862201 prefixEnd_862201 := by exact prefixLift 862201
  have htrace : WordTrace (prefixWord ++ tailWord_862201) baseStart_862201 baseEnd_862201 := by
    simpa [prefixWord, tailWord_862201, baseEnd_862201] using wordTrace_append hprefix tailTrace_862201
  have hstable : (prefixWord ++ tailWord_862201).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_862201).length < 2 ^ (prefixWord ++ tailWord_862201).sum := by decide
  have hdescent : baseEnd_862201 < baseStart_862201 := by decide
  rcases family_descends (prefixWord ++ tailWord_862201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_862218 : List Nat := [3, 1, 2, 2, 5, 1, 6]
def baseStart_862218 : Nat := 118140960795 + 862218 * 2 ^ 59
def prefixEnd_862218 : Nat := 4983230072969 + 3 ^ 40 * 862218 * 2
def baseEnd_862218 : Nat := 43726643255151881660221

theorem tailTrace_862218 : CollatzResearch.WordTrace tailWord_862218 prefixEnd_862218 43726643255151881660221 := by
  unfold tailWord_862218
  simp only [CollatzResearch.WordTrace]
  refine ⟨7861918497584728988982827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20965115993559277303954205 7861918497584728988982827)
  ·
    refine ⟨11792877746377093483474241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7861918497584728988982827 11792877746377093483474241)
    ·
      refine ⟨8844658309782820112605681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11792877746377093483474241 8844658309782820112605681)
      ·
        refine ⟨6633493732337115084454261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8844658309782820112605681 6633493732337115084454261)
        ·
          refine ⟨621890037406604539167587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6633493732337115084454261 621890037406604539167587)
          ·
            refine ⟨932835056109906808751381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 621890037406604539167587 932835056109906808751381)
            ·
              refine ⟨43726643255151881660221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 932835056109906808751381 43726643255151881660221)
              ·
                rfl

theorem cell20_862218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 6].length) (baseStart_862218 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_862218 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_862218 prefixEnd_862218 := by exact prefixLift 862218
  have htrace : WordTrace (prefixWord ++ tailWord_862218) baseStart_862218 baseEnd_862218 := by
    simpa [prefixWord, tailWord_862218, baseEnd_862218] using wordTrace_append hprefix tailTrace_862218
  have hstable : (prefixWord ++ tailWord_862218).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_862218).length < 2 ^ (prefixWord ++ tailWord_862218).sum := by decide
  have hdescent : baseEnd_862218 < baseStart_862218 := by decide
  rcases family_descends (prefixWord ++ tailWord_862218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_862284 : List Nat := [2, 2, 1, 3, 1, 1, 3, 4, 3]
def baseStart_862284 : Nat := 118140960795 + 862284 * 2 ^ 59
def prefixEnd_862284 : Nat := 4983230072969 + 3 ^ 40 * 862284 * 2
def baseEnd_862284 : Nat := 393569913494764038741719

theorem tailTrace_862284 : CollatzResearch.WordTrace tailWord_862284 prefixEnd_862284 393569913494764038741719 := by
  unfold tailWord_862284
  simp only [CollatzResearch.WordTrace]
  refine ⟨15725040604049904613916953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20966720805399872818555937 15725040604049904613916953)
  ·
    refine ⟨11793780453037428460437715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15725040604049904613916953 11793780453037428460437715)
    ·
      refine ⟨17690670679556142690656573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11793780453037428460437715 17690670679556142690656573)
      ·
        refine ⟨6634001504833553508996215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17690670679556142690656573 6634001504833553508996215)
        ·
          refine ⟨9951002257250330263494323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6634001504833553508996215 9951002257250330263494323)
          ·
            refine ⟨14926503385875495395241485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9951002257250330263494323 14926503385875495395241485)
            ·
              refine ⟨5597438769703310773215557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14926503385875495395241485 5597438769703310773215557)
              ·
                refine ⟨1049519769319370769977917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5597438769703310773215557 1049519769319370769977917)
                ·
                  refine ⟨393569913494764038741719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1049519769319370769977917 393569913494764038741719)
                  ·
                    rfl

theorem cell20_862284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 4, 3].length) (baseStart_862284 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_862284 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_862284 prefixEnd_862284 := by exact prefixLift 862284
  have htrace : WordTrace (prefixWord ++ tailWord_862284) baseStart_862284 baseEnd_862284 := by
    simpa [prefixWord, tailWord_862284, baseEnd_862284] using wordTrace_append hprefix tailTrace_862284
  have hstable : (prefixWord ++ tailWord_862284).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_862284).length < 2 ^ (prefixWord ++ tailWord_862284).sum := by decide
  have hdescent : baseEnd_862284 < baseStart_862284 := by decide
  rcases family_descends (prefixWord ++ tailWord_862284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_862305 : List Nat := [1, 2, 3, 1, 1, 2, 1, 2, 7]
def baseStart_862305 : Nat := 118140960795 + 862305 * 2 ^ 59
def prefixEnd_862305 : Nat := 4983230072969 + 3 ^ 40 * 862305 * 2
def baseEnd_862305 : Nat := 393579498466981299041633

theorem tailTrace_862305 : CollatzResearch.WordTrace tailWord_862305 prefixEnd_862305 393579498466981299041633 := by
  unfold tailWord_862305
  simp only [CollatzResearch.WordTrace]
  refine ⟨31450847141023729814348369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20967231427349153209565579 31450847141023729814348369)
  ·
    refine ⟨23588135355767797360761277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31450847141023729814348369 23588135355767797360761277)
    ·
      refine ⟨8845550758412924010285479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23588135355767797360761277 8845550758412924010285479)
      ·
        refine ⟨13268326137619386015428219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8845550758412924010285479 13268326137619386015428219)
        ·
          refine ⟨19902489206429079023142329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13268326137619386015428219 19902489206429079023142329)
          ·
            refine ⟨14926866904821809267356747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19902489206429079023142329 14926866904821809267356747)
            ·
              refine ⟨22390300357232713901035121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14926866904821809267356747 22390300357232713901035121)
              ·
                refine ⟨16792725267924535425776341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22390300357232713901035121 16792725267924535425776341)
                ·
                  refine ⟨393579498466981299041633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16792725267924535425776341 393579498466981299041633)
                  ·
                    rfl

theorem cell20_862305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 2, 7].length) (baseStart_862305 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_862305 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_862305 prefixEnd_862305 := by exact prefixLift 862305
  have htrace : WordTrace (prefixWord ++ tailWord_862305) baseStart_862305 baseEnd_862305 := by
    simpa [prefixWord, tailWord_862305, baseEnd_862305] using wordTrace_append hprefix tailTrace_862305
  have hstable : (prefixWord ++ tailWord_862305).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_862305).length < 2 ^ (prefixWord ++ tailWord_862305).sum := by decide
  have hdescent : baseEnd_862305 < baseStart_862305 := by decide
  rcases family_descends (prefixWord ++ tailWord_862305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_862339 : List Nat := [1, 1, 1, 3, 3, 5, 1, 2, 3]
def baseStart_862339 : Nat := 118140960795 + 862339 * 2 ^ 59
def prefixEnd_862339 : Nat := 4983230072969 + 3 ^ 40 * 862339 * 2
def baseEnd_862339 : Nat := 393595016993428291908161

theorem tailTrace_862339 : CollatzResearch.WordTrace tailWord_862339 prefixEnd_862339 393595016993428291908161 := by
  unfold tailWord_862339
  simp only [CollatzResearch.WordTrace]
  refine ⟨31452087222900553621086071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20968058148600369080724047 31452087222900553621086071)
  ·
    refine ⟨47178130834350830431629107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31452087222900553621086071 47178130834350830431629107)
    ·
      refine ⟨70767196251526245647443661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47178130834350830431629107 70767196251526245647443661)
      ·
        refine ⟨26537698594322342117791373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70767196251526245647443661 26537698594322342117791373)
        ·
          refine ⟨9951636972870878294171765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26537698594322342117791373 9951636972870878294171765)
          ·
            refine ⟨932965966206644840078603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9951636972870878294171765 932965966206644840078603)
            ·
              refine ⟨1399448949309967260117905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 932965966206644840078603 1399448949309967260117905)
              ·
                refine ⟨1049586711982475445088429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1399448949309967260117905 1049586711982475445088429)
                ·
                  refine ⟨393595016993428291908161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1049586711982475445088429 393595016993428291908161)
                  ·
                    rfl

theorem cell20_862339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 1, 2, 3].length) (baseStart_862339 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_862339 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_862339 prefixEnd_862339 := by exact prefixLift 862339
  have htrace : WordTrace (prefixWord ++ tailWord_862339) baseStart_862339 baseEnd_862339 := by
    simpa [prefixWord, tailWord_862339, baseEnd_862339] using wordTrace_append hprefix tailTrace_862339
  have hstable : (prefixWord ++ tailWord_862339).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_862339).length < 2 ^ (prefixWord ++ tailWord_862339).sum := by decide
  have hdescent : baseEnd_862339 < baseStart_862339 := by decide
  rcases family_descends (prefixWord ++ tailWord_862339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_862346 : List Nat := [3, 1, 2, 3, 1, 3, 2, 1, 4]
def baseStart_862346 : Nat := 118140960795 + 862346 * 2 ^ 59
def prefixEnd_862346 : Nat := 4983230072969 + 3 ^ 40 * 862346 * 2
def baseEnd_862346 : Nat := 393598211984167378674799

theorem tailTrace_862346 : CollatzResearch.WordTrace tailWord_862346 prefixEnd_862346 393598211984167378674799 := by
  unfold tailWord_862346
  simp only [CollatzResearch.WordTrace]
  refine ⟨7863085633468798454147723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20968228355916795877727261 7863085633468798454147723)
  ·
    refine ⟨11794628450203197681221585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7863085633468798454147723 11794628450203197681221585)
    ·
      refine ⟨8845971337652398260916189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11794628450203197681221585 8845971337652398260916189)
      ·
        refine ⟨3317239251619649347843571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8845971337652398260916189 3317239251619649347843571)
        ·
          refine ⟨4975858877429474021765357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3317239251619649347843571 4975858877429474021765357)
          ·
            refine ⟨1865947079036052758162009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4975858877429474021765357 1865947079036052758162009)
            ·
              refine ⟨1399460309277039568621507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1865947079036052758162009 1399460309277039568621507)
              ·
                refine ⟨2099190463915559352932261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1399460309277039568621507 2099190463915559352932261)
                ·
                  refine ⟨393598211984167378674799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2099190463915559352932261 393598211984167378674799)
                  ·
                    rfl

theorem cell20_862346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 2, 1, 4].length) (baseStart_862346 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_862346 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_862346 prefixEnd_862346 := by exact prefixLift 862346
  have htrace : WordTrace (prefixWord ++ tailWord_862346) baseStart_862346 baseEnd_862346 := by
    simpa [prefixWord, tailWord_862346, baseEnd_862346] using wordTrace_append hprefix tailTrace_862346
  have hstable : (prefixWord ++ tailWord_862346).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_862346).length < 2 ^ (prefixWord ++ tailWord_862346).sum := by decide
  have hdescent : baseEnd_862346 < baseStart_862346 := by decide
  rcases family_descends (prefixWord ++ tailWord_862346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_862366 : List Nat := [4, 3, 1, 1, 4, 1, 2, 4]
def baseStart_862366 : Nat := 118140960795 + 862366 * 2 ^ 59
def prefixEnd_862366 : Nat := 4983230072969 + 3 ^ 40 * 862366 * 2
def baseEnd_862366 : Nat := 131202446843045399336017

theorem tailTrace_862366 : CollatzResearch.WordTrace tailWord_862366 prefixEnd_862366 131202446843045399336017 := by
  unfold tailWord_862366
  simp only [CollatzResearch.WordTrace]
  refine ⟨3931633999225342154039869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20968714662535158154879301 3931633999225342154039869)
  ·
    refine ⟨1474362749709503307764951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3931633999225342154039869 1474362749709503307764951)
    ·
      refine ⟨2211544124564254961647427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1474362749709503307764951 2211544124564254961647427)
      ·
        refine ⟨3317316186846382442471141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2211544124564254961647427 3317316186846382442471141)
        ·
          refine ⟨621996785033696707963339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3317316186846382442471141 621996785033696707963339)
          ·
            refine ⟨932995177550545061945009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 621996785033696707963339 932995177550545061945009)
            ·
              refine ⟨699746383162908796458757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 932995177550545061945009 699746383162908796458757)
              ·
                refine ⟨131202446843045399336017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 699746383162908796458757 131202446843045399336017)
                ·
                  rfl

theorem cell20_862366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 2, 4].length) (baseStart_862366 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_862366 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_862366 prefixEnd_862366 := by exact prefixLift 862366
  have htrace : WordTrace (prefixWord ++ tailWord_862366) baseStart_862366 baseEnd_862366 := by
    simpa [prefixWord, tailWord_862366, baseEnd_862366] using wordTrace_append hprefix tailTrace_862366
  have hstable : (prefixWord ++ tailWord_862366).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_862366).length < 2 ^ (prefixWord ++ tailWord_862366).sum := by decide
  have hdescent : baseEnd_862366 < baseStart_862366 := by decide
  rcases family_descends (prefixWord ++ tailWord_862366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_862370 : List Nat := [3, 3, 1, 3, 1, 1, 4, 4]
def baseStart_862370 : Nat := 118140960795 + 862370 * 2 ^ 59
def prefixEnd_862370 : Nat := 4983230072969 + 3 ^ 40 * 862370 * 2
def baseEnd_862370 : Nat := 131203055412709987291567

theorem tailTrace_862370 : CollatzResearch.WordTrace tailWord_862370 prefixEnd_862370 131203055412709987291567 := by
  unfold tailWord_862370
  simp only [CollatzResearch.WordTrace]
  refine ⟨7863304471447061478866141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20968811923858830610309709 7863304471447061478866141)
  ·
    refine ⟨2948739176792648054574803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7863304471447061478866141 2948739176792648054574803)
    ·
      refine ⟨4423108765188972081862205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2948739176792648054574803 4423108765188972081862205)
      ·
        refine ⟨1658665786945864530698327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4423108765188972081862205 1658665786945864530698327)
        ·
          refine ⟨2487998680418796796047491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1658665786945864530698327 2487998680418796796047491)
          ·
            refine ⟨3731998020628195194071237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2487998680418796796047491 3731998020628195194071237)
            ·
              refine ⟨699749628867786598888357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3731998020628195194071237 699749628867786598888357)
              ·
                refine ⟨131203055412709987291567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 699749628867786598888357 131203055412709987291567)
                ·
                  rfl

theorem cell20_862370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 4, 4].length) (baseStart_862370 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_862370 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_862370 prefixEnd_862370 := by exact prefixLift 862370
  have htrace : WordTrace (prefixWord ++ tailWord_862370) baseStart_862370 baseEnd_862370 := by
    simpa [prefixWord, tailWord_862370, baseEnd_862370] using wordTrace_append hprefix tailTrace_862370
  have hstable : (prefixWord ++ tailWord_862370).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_862370).length < 2 ^ (prefixWord ++ tailWord_862370).sum := by decide
  have hdescent : baseEnd_862370 < baseStart_862370 := by decide
  rcases family_descends (prefixWord ++ tailWord_862370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_862405 : List Nat := [1, 3, 1, 1, 1, 1, 7, 1, 4]
def baseStart_862405 : Nat := 118140960795 + 862405 * 2 ^ 59
def prefixEnd_862405 : Nat := 4983230072969 + 3 ^ 40 * 862405 * 2
def baseEnd_862405 : Nat := 393625141191825395707891

theorem tailTrace_862405 : CollatzResearch.WordTrace tailWord_862405 prefixEnd_862405 393625141191825395707891 := by
  unfold tailWord_862405
  simp only [CollatzResearch.WordTrace]
  refine ⟨31454494440661446892988669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20969662960440964595325779 31454494440661446892988669)
  ·
    refine ⟨11795435415248042584870751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31454494440661446892988669 11795435415248042584870751)
    ·
      refine ⟨17693153122872063877306127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11795435415248042584870751 17693153122872063877306127)
      ·
        refine ⟨26539729684308095815959191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17693153122872063877306127 26539729684308095815959191)
        ·
          refine ⟨39809594526462143723938787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26539729684308095815959191 39809594526462143723938787)
          ·
            refine ⟨59714391789693215585908181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39809594526462143723938787 59714391789693215585908181)
            ·
              refine ⟨1399556057570934740294723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 59714391789693215585908181 1399556057570934740294723)
              ·
                refine ⟨2099334086356402110442085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1399556057570934740294723 2099334086356402110442085)
                ·
                  refine ⟨393625141191825395707891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2099334086356402110442085 393625141191825395707891)
                  ·
                    rfl

theorem cell20_862405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 7, 1, 4].length) (baseStart_862405 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_862405 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_862405 prefixEnd_862405 := by exact prefixLift 862405
  have htrace : WordTrace (prefixWord ++ tailWord_862405) baseStart_862405 baseEnd_862405 := by
    simpa [prefixWord, tailWord_862405, baseEnd_862405] using wordTrace_append hprefix tailTrace_862405
  have hstable : (prefixWord ++ tailWord_862405).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_862405).length < 2 ^ (prefixWord ++ tailWord_862405).sum := by decide
  have hdescent : baseEnd_862405 < baseStart_862405 := by decide
  rcases family_descends (prefixWord ++ tailWord_862405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_862429 : List Nat := [1, 4, 3, 2, 1, 1, 2, 6]
def baseStart_862429 : Nat := 118140960795 + 862429 * 2 ^ 59
def prefixEnd_862429 : Nat := 4983230072969 + 3 ^ 40 * 862429 * 2
def baseEnd_862429 : Nat := 131212031815262659635931

theorem tailTrace_862429 : CollatzResearch.WordTrace tailWord_862429 prefixEnd_862429 131212031815262659635931 := by
  unfold tailWord_862429
  simp only [CollatzResearch.WordTrace]
  refine ⟨31455369792574498991862341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20970246528382999327908227 31455369792574498991862341)
  ·
    refine ⟨5897881836107718560974189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31455369792574498991862341 5897881836107718560974189)
    ·
      refine ⟨2211705688540394460365321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5897881836107718560974189 2211705688540394460365321)
      ·
        refine ⟨1658779266405295845273991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2211705688540394460365321 1658779266405295845273991)
        ·
          refine ⟨2488168899607943767910987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1658779266405295845273991 2488168899607943767910987)
          ·
            refine ⟨3732253349411915651866481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2488168899607943767910987 3732253349411915651866481)
            ·
              refine ⟨2799190012058936738899861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3732253349411915651866481 2799190012058936738899861)
              ·
                refine ⟨131212031815262659635931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2799190012058936738899861 131212031815262659635931)
                ·
                  rfl

theorem cell20_862429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 2, 6].length) (baseStart_862429 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_862429 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_862429 prefixEnd_862429 := by exact prefixLift 862429
  have htrace : WordTrace (prefixWord ++ tailWord_862429) baseStart_862429 baseEnd_862429 := by
    simpa [prefixWord, tailWord_862429, baseEnd_862429] using wordTrace_append hprefix tailTrace_862429
  have hstable : (prefixWord ++ tailWord_862429).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_862429).length < 2 ^ (prefixWord ++ tailWord_862429).sum := by decide
  have hdescent : baseEnd_862429 < baseStart_862429 := by decide
  rcases family_descends (prefixWord ++ tailWord_862429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_862450 : List Nat := [3, 2, 1, 3, 2, 9]
def baseStart_862450 : Nat := 118140960795 + 862450 * 2 ^ 59
def prefixEnd_862450 : Nat := 4983230072969 + 3 ^ 40 * 862450 * 2
def baseEnd_862450 : Nat := 14579469645111305155841

theorem tailTrace_862450 : CollatzResearch.WordTrace tailWord_862450 prefixEnd_862450 14579469645111305155841 := by
  unfold tailWord_862450
  simp only [CollatzResearch.WordTrace]
  refine ⟨7864033931374604894594201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20970757150332279718917869 7864033931374604894594201)
  ·
    refine ⟨5898025448530953670945651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7864033931374604894594201 5898025448530953670945651)
    ·
      refine ⟨8847038172796430506418477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5898025448530953670945651 8847038172796430506418477)
      ·
        refine ⟨3317639314798661439906929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8847038172796430506418477 3317639314798661439906929)
        ·
          refine ⟨2488229486098996079930197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3317639314798661439906929 2488229486098996079930197)
          ·
            refine ⟨14579469645111305155841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2488229486098996079930197 14579469645111305155841)
            ·
              rfl

theorem cell20_862450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 9].length) (baseStart_862450 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_862450 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_862450 prefixEnd_862450 := by exact prefixLift 862450
  have htrace : WordTrace (prefixWord ++ tailWord_862450) baseStart_862450 baseEnd_862450 := by
    simpa [prefixWord, tailWord_862450, baseEnd_862450] using wordTrace_append hprefix tailTrace_862450
  have hstable : (prefixWord ++ tailWord_862450).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_862450).length < 2 ^ (prefixWord ++ tailWord_862450).sum := by decide
  have hdescent : baseEnd_862450 < baseStart_862450 := by decide
  rcases family_descends (prefixWord ++ tailWord_862450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_862474 : List Nat := [3, 1, 2, 2, 1, 1, 4, 3, 3]
def baseStart_862474 : Nat := 118140960795 + 862474 * 2 ^ 59
def prefixEnd_862474 : Nat := 4983230072969 + 3 ^ 40 * 862474 * 2
def baseEnd_862474 : Nat := 393656634671967822407609

theorem tailTrace_862474 : CollatzResearch.WordTrace tailWord_862474 prefixEnd_862474 393656634671967822407609 := by
  unfold tailWord_862474
  simp only [CollatzResearch.WordTrace]
  refine ⟨7864252769352867919312619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20971340718274314451500317 7864252769352867919312619)
  ·
    refine ⟨11796379154029301878968929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7864252769352867919312619 11796379154029301878968929)
    ·
      refine ⟨8847284365521976409226697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11796379154029301878968929 8847284365521976409226697)
      ·
        refine ⟨6635463274141482306920023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8847284365521976409226697 6635463274141482306920023)
        ·
          refine ⟨9953194911212223460380035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6635463274141482306920023 9953194911212223460380035)
          ·
            refine ⟨14929792366818335190570053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9953194911212223460380035 14929792366818335190570053)
            ·
              refine ⟨2799336068778437848231885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14929792366818335190570053 2799336068778437848231885)
              ·
                refine ⟨1049751025791914193086957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2799336068778437848231885 1049751025791914193086957)
                ·
                  refine ⟨393656634671967822407609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1049751025791914193086957 393656634671967822407609)
                  ·
                    rfl

theorem cell20_862474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 4, 3, 3].length) (baseStart_862474 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_862474 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_862474 prefixEnd_862474 := by exact prefixLift 862474
  have htrace : WordTrace (prefixWord ++ tailWord_862474) baseStart_862474 baseEnd_862474 := by
    simpa [prefixWord, tailWord_862474, baseEnd_862474] using wordTrace_append hprefix tailTrace_862474
  have hstable : (prefixWord ++ tailWord_862474).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_862474).length < 2 ^ (prefixWord ++ tailWord_862474).sum := by decide
  have hdescent : baseEnd_862474 < baseStart_862474 := by decide
  rcases family_descends (prefixWord ++ tailWord_862474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_862481 : List Nat := [1, 2, 2, 1, 1, 6, 1, 2, 4]
def baseStart_862481 : Nat := 118140960795 + 862481 * 2 ^ 59
def prefixEnd_862481 : Nat := 4983230072969 + 3 ^ 40 * 862481 * 2
def baseEnd_862481 : Nat := 393659829662706909174247

theorem tailTrace_862481 : CollatzResearch.WordTrace tailWord_862481 prefixEnd_862481 393659829662706909174247 := by
  unfold tailWord_862481
  simp only [CollatzResearch.WordTrace]
  refine ⟨31457266388386111872755297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20971510925590741248503531 31457266388386111872755297)
  ·
    refine ⟨23592949791289583904566473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31457266388386111872755297 23592949791289583904566473)
    ·
      refine ⟨17694712343467187928424855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23592949791289583904566473 17694712343467187928424855)
      ·
        refine ⟨26542068515200781892637283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17694712343467187928424855 26542068515200781892637283)
        ·
          refine ⟨39813102772801172838955925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26542068515200781892637283 39813102772801172838955925)
          ·
            refine ⟨1866239192475054976826059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 39813102772801172838955925 1866239192475054976826059)
            ·
              refine ⟨2799358788712582465239089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1866239192475054976826059 2799358788712582465239089)
              ·
                refine ⟨2099519091534436848929317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2799358788712582465239089 2099519091534436848929317)
                ·
                  refine ⟨393659829662706909174247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2099519091534436848929317 393659829662706909174247)
                  ·
                    rfl

theorem cell20_862481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 1, 2, 4].length) (baseStart_862481 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_862481 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_862481 prefixEnd_862481 := by exact prefixLift 862481
  have htrace : WordTrace (prefixWord ++ tailWord_862481) baseStart_862481 baseEnd_862481 := by
    simpa [prefixWord, tailWord_862481, baseEnd_862481] using wordTrace_append hprefix tailTrace_862481
  have hstable : (prefixWord ++ tailWord_862481).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_862481).length < 2 ^ (prefixWord ++ tailWord_862481).sum := by decide
  have hdescent : baseEnd_862481 < baseStart_862481 := by decide
  rcases family_descends (prefixWord ++ tailWord_862481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_862494 : List Nat := [4, 3, 2, 1, 1, 1, 1, 5, 2]
def baseStart_862494 : Nat := 118140960795 + 862494 * 2 ^ 59
def prefixEnd_862494 : Nat := 4983230072969 + 3 ^ 40 * 862494 * 2
def baseEnd_862494 : Nat := 393665763216936641740861

theorem tailTrace_862494 : CollatzResearch.WordTrace tailWord_862494 prefixEnd_862494 393665763216936641740861 := by
  unfold tailWord_862494
  simp only [CollatzResearch.WordTrace]
  refine ⟨3932217567167376886622317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20971827024892676728652357 3932217567167376886622317)
  ·
    refine ⟨1474581587687766332483369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3932217567167376886622317 1474581587687766332483369)
    ·
      refine ⟨1105936190765824749362527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1474581587687766332483369 1105936190765824749362527)
      ·
        refine ⟨1658904286148737124043791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1105936190765824749362527 1658904286148737124043791)
        ·
          refine ⟨2488356429223105686065687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1658904286148737124043791 2488356429223105686065687)
          ·
            refine ⟨3732534643834658529098531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2488356429223105686065687 3732534643834658529098531)
            ·
              refine ⟨5598801965751987793647797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3732534643834658529098531 5598801965751987793647797)
              ·
                refine ⟨524887684289248855654481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5598801965751987793647797 524887684289248855654481)
                ·
                  refine ⟨393665763216936641740861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 524887684289248855654481 393665763216936641740861)
                  ·
                    rfl

theorem cell20_862494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 5, 2].length) (baseStart_862494 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_862494 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_862494 prefixEnd_862494 := by exact prefixLift 862494
  have htrace : WordTrace (prefixWord ++ tailWord_862494) baseStart_862494 baseEnd_862494 := by
    simpa [prefixWord, tailWord_862494, baseEnd_862494] using wordTrace_append hprefix tailTrace_862494
  have hstable : (prefixWord ++ tailWord_862494).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_862494).length < 2 ^ (prefixWord ++ tailWord_862494).sum := by decide
  have hdescent : baseEnd_862494 < baseStart_862494 := by decide
  rcases family_descends (prefixWord ++ tailWord_862494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_862570 : List Nat := [3, 1, 3, 3, 1, 2, 3, 2, 2]
def baseStart_862570 : Nat := 118140960795 + 862570 * 2 ^ 59
def prefixEnd_862570 : Nat := 4983230072969 + 3 ^ 40 * 862570 * 2
def baseEnd_862570 : Nat := 393700451687818155207217

theorem tailTrace_862570 : CollatzResearch.WordTrace tailWord_862570 prefixEnd_862570 393700451687818155207217 := by
  unfold tailWord_862570
  simp only [CollatzResearch.WordTrace]
  refine ⟨7865128121265920018186291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20973674990042453381830109 7865128121265920018186291)
  ·
    refine ⟨11797692181898880027279437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7865128121265920018186291 11797692181898880027279437)
    ·
      refine ⟨4424134568212080010229789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11797692181898880027279437 4424134568212080010229789)
      ·
        refine ⟨1659050463079530003836171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4424134568212080010229789 1659050463079530003836171)
        ·
          refine ⟨2488575694619295005754257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1659050463079530003836171 2488575694619295005754257)
          ·
            refine ⟨1866431770964471254315693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2488575694619295005754257 1866431770964471254315693)
            ·
              refine ⟨699911914111676720368385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1866431770964471254315693 699911914111676720368385)
              ·
                refine ⟨524933935583757540276289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 699911914111676720368385 524933935583757540276289)
                ·
                  refine ⟨393700451687818155207217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 524933935583757540276289 393700451687818155207217)
                  ·
                    rfl

theorem cell20_862570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 3, 2, 2].length) (baseStart_862570 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_862570 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_862570 prefixEnd_862570 := by exact prefixLift 862570
  have htrace : WordTrace (prefixWord ++ tailWord_862570) baseStart_862570 baseEnd_862570 := by
    simpa [prefixWord, tailWord_862570, baseEnd_862570] using wordTrace_append hprefix tailTrace_862570
  have hstable : (prefixWord ++ tailWord_862570).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_862570).length < 2 ^ (prefixWord ++ tailWord_862570).sum := by decide
  have hdescent : baseEnd_862570 < baseStart_862570 := by decide
  rcases family_descends (prefixWord ++ tailWord_862570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_862581 : List Nat := [1, 3, 4, 1, 2, 2, 2, 5]
def baseStart_862581 : Nat := 118140960795 + 862581 * 2 ^ 59
def prefixEnd_862581 : Nat := 4983230072969 + 3 ^ 40 * 862581 * 2
def baseEnd_862581 : Nat := 131235157462517001946835

theorem tailTrace_862581 : CollatzResearch.WordTrace tailWord_862581 prefixEnd_862581 131235157462517001946835 := by
  unfold tailWord_862581
  simp only [CollatzResearch.WordTrace]
  refine ⟨31460913688023828951395597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20973942458682552634263731 31460913688023828951395597)
  ·
    refine ⟨11797842633008935856773349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31460913688023828951395597 11797842633008935856773349)
    ·
      refine ⟨2212095493689175473145003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11797842633008935856773349 2212095493689175473145003)
      ·
        refine ⟨3318143240533763209717505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2212095493689175473145003 3318143240533763209717505)
        ·
          refine ⟨2488607430400322407288129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3318143240533763209717505 2488607430400322407288129)
          ·
            refine ⟨1866455572800241805466097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2488607430400322407288129 1866455572800241805466097)
            ·
              refine ⟨1399841679600181354099573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1866455572800241805466097 1399841679600181354099573)
              ·
                refine ⟨131235157462517001946835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1399841679600181354099573 131235157462517001946835)
                ·
                  rfl

theorem cell20_862581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 2, 5].length) (baseStart_862581 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_862581 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_862581 prefixEnd_862581 := by exact prefixLift 862581
  have htrace : WordTrace (prefixWord ++ tailWord_862581) baseStart_862581 baseEnd_862581 := by
    simpa [prefixWord, tailWord_862581, baseEnd_862581] using wordTrace_append hprefix tailTrace_862581
  have hstable : (prefixWord ++ tailWord_862581).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_862581).length < 2 ^ (prefixWord ++ tailWord_862581).sum := by decide
  have hdescent : baseEnd_862581 < baseStart_862581 := by decide
  rcases family_descends (prefixWord ++ tailWord_862581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_862622 : List Nat := [4, 3, 1, 2, 1, 2, 2, 2, 3]
def baseStart_862622 : Nat := 118140960795 + 862622 * 2 ^ 59
def prefixEnd_862622 : Nat := 4983230072969 + 3 ^ 40 * 862622 * 2
def baseEnd_862622 : Nat := 393724185904737085473671

theorem tailTrace_862622 : CollatzResearch.WordTrace tailWord_862622 prefixEnd_862622 393724185904737085473671 := by
  unfold tailWord_862622
  simp only [CollatzResearch.WordTrace]
  refine ⟨3932801135109411619204765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20974939387250195302425413 3932801135109411619204765)
  ·
    refine ⟨1474800425666029357201787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3932801135109411619204765 1474800425666029357201787)
    ·
      refine ⟨2212200638499044035802681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1474800425666029357201787 2212200638499044035802681)
      ·
        refine ⟨1659150478874283026852011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2212200638499044035802681 1659150478874283026852011)
        ·
          refine ⟨2488725718311424540278017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1659150478874283026852011 2488725718311424540278017)
          ·
            refine ⟨1866544288733568405208513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2488725718311424540278017 1866544288733568405208513)
            ·
              refine ⟨1399908216550176303906385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1866544288733568405208513 1399908216550176303906385)
              ·
                refine ⟨1049931162412632227929789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1399908216550176303906385 1049931162412632227929789)
                ·
                  refine ⟨393724185904737085473671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1049931162412632227929789 393724185904737085473671)
                  ·
                    rfl

theorem cell20_862622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 2, 2, 3].length) (baseStart_862622 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_862622 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_862622 prefixEnd_862622 := by exact prefixLift 862622
  have htrace : WordTrace (prefixWord ++ tailWord_862622) baseStart_862622 baseEnd_862622 := by
    simpa [prefixWord, tailWord_862622, baseEnd_862622] using wordTrace_append hprefix tailTrace_862622
  have hstable : (prefixWord ++ tailWord_862622).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_862622).length < 2 ^ (prefixWord ++ tailWord_862622).sum := by decide
  have hdescent : baseEnd_862622 < baseStart_862622 := by decide
  rcases family_descends (prefixWord ++ tailWord_862622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_862625 : List Nat := [1, 2, 3, 5, 1, 2, 2, 2, 2]
def baseStart_862625 : Nat := 118140960795 + 862625 * 2 ^ 59
def prefixEnd_862625 : Nat := 4983230072969 + 3 ^ 40 * 862625 * 2
def baseEnd_862625 : Nat := 393725555186482408373659

theorem tailTrace_862625 : CollatzResearch.WordTrace tailWord_862625 prefixEnd_862625 393725555186482408373659 := by
  unfold tailWord_862625
  simp only [CollatzResearch.WordTrace]
  refine ⟨31462518499864424465997329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20975012333242949643998219 31462518499864424465997329)
  ·
    refine ⟨23596888874898318349497997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31462518499864424465997329 23596888874898318349497997)
    ·
      refine ⟨8848833328086869381061749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23596888874898318349497997 8848833328086869381061749)
      ·
        refine ⟨829578124508144004474539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8848833328086869381061749 829578124508144004474539)
        ·
          refine ⟨1244367186762216006711809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 829578124508144004474539 1244367186762216006711809)
          ·
            refine ⟨933275390071662005033857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1244367186762216006711809 933275390071662005033857)
            ·
              refine ⟨699956542553746503775393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 933275390071662005033857 699956542553746503775393)
              ·
                refine ⟨524967406915309877831545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 699956542553746503775393 524967406915309877831545)
                ·
                  refine ⟨393725555186482408373659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 524967406915309877831545 393725555186482408373659)
                  ·
                    rfl

theorem cell20_862625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 2, 2, 2].length) (baseStart_862625 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_862625 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_862625 prefixEnd_862625 := by exact prefixLift 862625
  have htrace : WordTrace (prefixWord ++ tailWord_862625) baseStart_862625 baseEnd_862625 := by
    simpa [prefixWord, tailWord_862625, baseEnd_862625] using wordTrace_append hprefix tailTrace_862625
  have hstable : (prefixWord ++ tailWord_862625).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_862625).length < 2 ^ (prefixWord ++ tailWord_862625).sum := by decide
  have hdescent : baseEnd_862625 < baseStart_862625 := by decide
  rcases family_descends (prefixWord ++ tailWord_862625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_862699 : List Nat := [1, 1, 1, 1, 2, 3, 4, 7]
def baseStart_862699 : Nat := 118140960795 + 862699 * 2 ^ 59
def prefixEnd_862699 : Nat := 4983230072969 + 3 ^ 40 * 862699 * 2
def baseEnd_862699 : Nat := 131253110267622346635563

theorem tailTrace_862699 : CollatzResearch.WordTrace tailWord_862699 prefixEnd_862699 131253110267622346635563 := by
  unfold tailWord_862699
  simp only [CollatzResearch.WordTrace]
  refine ⟨31465217501596335104191151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20976811667730890069460767 31465217501596335104191151)
  ·
    refine ⟨47197826252394502656286727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31465217501596335104191151 47197826252394502656286727)
    ·
      refine ⟨70796739378591753984430091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47197826252394502656286727 70796739378591753984430091)
      ·
        refine ⟨106195109067887630976645137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70796739378591753984430091 106195109067887630976645137)
        ·
          refine ⟨79646331800915723232483853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106195109067887630976645137 79646331800915723232483853)
          ·
            refine ⟨29867374425343396212181445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79646331800915723232483853 29867374425343396212181445)
            ·
              refine ⟨5600132704751886789784021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29867374425343396212181445 5600132704751886789784021)
              ·
                refine ⟨131253110267622346635563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5600132704751886789784021 131253110267622346635563)
                ·
                  rfl

theorem cell20_862699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 7].length) (baseStart_862699 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_862699 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_862699 prefixEnd_862699 := by exact prefixLift 862699
  have htrace : WordTrace (prefixWord ++ tailWord_862699) baseStart_862699 baseEnd_862699 := by
    simpa [prefixWord, tailWord_862699, baseEnd_862699] using wordTrace_append hprefix tailTrace_862699
  have hstable : (prefixWord ++ tailWord_862699).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_862699).length < 2 ^ (prefixWord ++ tailWord_862699).sum := by decide
  have hdescent : baseEnd_862699 < baseStart_862699 := by decide
  rcases family_descends (prefixWord ++ tailWord_862699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_862743 : List Nat := [1, 1, 3, 6, 1, 2, 1, 1, 4]
def baseStart_862743 : Nat := 118140960795 + 862743 * 2 ^ 59
def prefixEnd_862743 : Nat := 4983230072969 + 3 ^ 40 * 862743 * 2
def baseEnd_862743 : Nat := 393779413601798442439843

theorem tailTrace_862743 : CollatzResearch.WordTrace tailWord_862743 prefixEnd_862743 393779413601798442439843 := by
  unfold tailWord_862743
  simp only [CollatzResearch.WordTrace]
  refine ⟨31466822313436930618792883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20977881542291287079195255 31466822313436930618792883)
  ·
    refine ⟨47200233470155395928189325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31466822313436930618792883 47200233470155395928189325)
    ·
      refine ⟨17700087551308273473070997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47200233470155395928189325 17700087551308273473070997)
      ·
        refine ⟨829691603967575319050203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 17700087551308273473070997 829691603967575319050203)
        ·
          refine ⟨1244537405951362978575305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 829691603967575319050203 1244537405951362978575305)
          ·
            refine ⟨933403054463522233931479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1244537405951362978575305 933403054463522233931479)
            ·
              refine ⟨1400104581695283350897219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 933403054463522233931479 1400104581695283350897219)
              ·
                refine ⟨2100156872542925026345829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1400104581695283350897219 2100156872542925026345829)
                ·
                  refine ⟨393779413601798442439843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2100156872542925026345829 393779413601798442439843)
                  ·
                    rfl

theorem cell20_862743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 1, 1, 4].length) (baseStart_862743 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_862743 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_862743 prefixEnd_862743 := by exact prefixLift 862743
  have htrace : WordTrace (prefixWord ++ tailWord_862743) baseStart_862743 baseEnd_862743 := by
    simpa [prefixWord, tailWord_862743, baseEnd_862743] using wordTrace_append hprefix tailTrace_862743
  have hstable : (prefixWord ++ tailWord_862743).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_862743).length < 2 ^ (prefixWord ++ tailWord_862743).sum := by decide
  have hdescent : baseEnd_862743 < baseStart_862743 := by decide
  rcases family_descends (prefixWord ++ tailWord_862743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_862768 : List Nat := [2, 1, 1, 1, 2, 3, 2, 4, 4]
def baseStart_862768 : Nat := 118140960795 + 862768 * 2 ^ 59
def prefixEnd_862768 : Nat := 4983230072969 + 3 ^ 40 * 862768 * 2
def baseEnd_862768 : Nat := 393790824283009466606407

theorem tailTrace_862768 : CollatzResearch.WordTrace tailWord_862768 prefixEnd_862768 393790824283009466606407 := by
  unfold tailWord_862768
  simp only [CollatzResearch.WordTrace]
  refine ⟨15733867069173179944226479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20978489425564239925635305 15733867069173179944226479)
  ·
    refine ⟨23600800603759769916339719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15733867069173179944226479 23600800603759769916339719)
    ·
      refine ⟨35401200905639654874509579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23600800603759769916339719 35401200905639654874509579)
      ·
        refine ⟨53101801358459482311764369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35401200905639654874509579 53101801358459482311764369)
        ·
          refine ⟨39826351018844611733823277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53101801358459482311764369 39826351018844611733823277)
          ·
            refine ⟨14934881632066729400183729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39826351018844611733823277 14934881632066729400183729)
            ·
              refine ⟨11201161224050047050137797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14934881632066729400183729 11201161224050047050137797)
              ·
                refine ⟨2100217729509383821900837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11201161224050047050137797 2100217729509383821900837)
                ·
                  refine ⟨393790824283009466606407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2100217729509383821900837 393790824283009466606407)
                  ·
                    rfl

theorem cell20_862768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 4, 4].length) (baseStart_862768 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_862768 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_862768 prefixEnd_862768 := by exact prefixLift 862768
  have htrace : WordTrace (prefixWord ++ tailWord_862768) baseStart_862768 baseEnd_862768 := by
    simpa [prefixWord, tailWord_862768, baseEnd_862768] using wordTrace_append hprefix tailTrace_862768
  have hstable : (prefixWord ++ tailWord_862768).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_862768).length < 2 ^ (prefixWord ++ tailWord_862768).sum := by decide
  have hdescent : baseEnd_862768 < baseStart_862768 := by decide
  rcases family_descends (prefixWord ++ tailWord_862768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_862775 : List Nat := [1, 1, 3, 1, 2, 3, 1, 8]
def baseStart_862775 : Nat := 118140960795 + 862775 * 2 ^ 59
def prefixEnd_862775 : Nat := 4983230072969 + 3 ^ 40 * 862775 * 2
def baseEnd_862775 : Nat := 131264673091249517791015

theorem tailTrace_862775 : CollatzResearch.WordTrace tailWord_862775 prefixEnd_862775 131264673091249517791015 := by
  unfold tailWord_862775
  simp only [CollatzResearch.WordTrace]
  refine ⟨31467989449321000083957779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20978659632880666722638519 31467989449321000083957779)
  ·
    refine ⟨47201984173981500125936669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31467989449321000083957779 47201984173981500125936669)
    ·
      refine ⟨17700744065243062547226251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47201984173981500125936669 17700744065243062547226251)
      ·
        refine ⟨26551116097864593820839377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17700744065243062547226251 26551116097864593820839377)
        ·
          refine ⟨19913337073398445365629533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26551116097864593820839377 19913337073398445365629533)
          ·
            refine ⟨7467501402524417012111075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19913337073398445365629533 7467501402524417012111075)
            ·
              refine ⟨11201252103786625518166613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7467501402524417012111075 11201252103786625518166613)
              ·
                refine ⟨131264673091249517791015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11201252103786625518166613 131264673091249517791015)
                ·
                  rfl

theorem cell20_862775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 8].length) (baseStart_862775 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_862775 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_862775 prefixEnd_862775 := by exact prefixLift 862775
  have htrace : WordTrace (prefixWord ++ tailWord_862775) baseStart_862775 baseEnd_862775 := by
    simpa [prefixWord, tailWord_862775, baseEnd_862775] using wordTrace_append hprefix tailTrace_862775
  have hstable : (prefixWord ++ tailWord_862775).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_862775).length < 2 ^ (prefixWord ++ tailWord_862775).sum := by decide
  have hdescent : baseEnd_862775 < baseStart_862775 := by decide
  rcases family_descends (prefixWord ++ tailWord_862775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_862788 : List Nat := [2, 3, 5, 1, 1, 8]
def baseStart_862788 : Nat := 118140960795 + 862788 * 2 ^ 59
def prefixEnd_862788 : Nat := 4983230072969 + 3 ^ 40 * 862788 * 2
def baseEnd_862788 : Nat := 14585183438073269849617

theorem tailTrace_862788 : CollatzResearch.WordTrace tailWord_862788 prefixEnd_862788 14585183438073269849617 := by
  unfold tailWord_862788
  simp only [CollatzResearch.WordTrace]
  refine ⟨15734231799136951652090509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20978975732182602202787345 15734231799136951652090509)
  ·
    refine ⟨5900336924676356869533941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15734231799136951652090509 5900336924676356869533941)
    ·
      refine ⟨553156586688408456518807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5900336924676356869533941 553156586688408456518807)
      ·
        refine ⟨829734880032612684778211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 553156586688408456518807 829734880032612684778211)
        ·
          refine ⟨1244602320048919027167317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 829734880032612684778211 1244602320048919027167317)
          ·
            refine ⟨14585183438073269849617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1244602320048919027167317 14585183438073269849617)
            ·
              rfl

theorem cell20_862788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 8].length) (baseStart_862788 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_862788 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_862788 prefixEnd_862788 := by exact prefixLift 862788
  have htrace : WordTrace (prefixWord ++ tailWord_862788) baseStart_862788 baseEnd_862788 := by
    simpa [prefixWord, tailWord_862788, baseEnd_862788] using wordTrace_append hprefix tailTrace_862788
  have hstable : (prefixWord ++ tailWord_862788).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_862788).length < 2 ^ (prefixWord ++ tailWord_862788).sum := by decide
  have hdescent : baseEnd_862788 < baseStart_862788 := by decide
  rcases family_descends (prefixWord ++ tailWord_862788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_862799 : List Nat := [1, 1, 2, 1, 1, 2, 5, 4, 3]
def baseStart_862799 : Nat := 118140960795 + 862799 * 2 ^ 59
def prefixEnd_862799 : Nat := 4983230072969 + 3 ^ 40 * 862799 * 2
def baseEnd_862799 : Nat := 393804973527711136572947

theorem tailTrace_862799 : CollatzResearch.WordTrace tailWord_862799 prefixEnd_862799 393804973527711136572947 := by
  unfold tailWord_862799
  simp only [CollatzResearch.WordTrace]
  refine ⟨31468864801234052182831451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20979243200822701455220967 31468864801234052182831451)
  ·
    refine ⟨47203297201851078274247177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31468864801234052182831451 47203297201851078274247177)
    ·
      refine ⟨35402472901388308705685383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47203297201851078274247177 35402472901388308705685383)
      ·
        refine ⟨53103709352082463058528075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35402472901388308705685383 53103709352082463058528075)
        ·
          refine ⟨79655564028123694587792113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53103709352082463058528075 79655564028123694587792113)
          ·
            refine ⟨59741673021092770940844085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79655564028123694587792113 59741673021092770940844085)
            ·
              refine ⟨5600781845727447275704133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 59741673021092770940844085 5600781845727447275704133)
              ·
                refine ⟨1050146596073896364194525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5600781845727447275704133 1050146596073896364194525)
                ·
                  refine ⟨393804973527711136572947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1050146596073896364194525 393804973527711136572947)
                  ·
                    rfl

theorem cell20_862799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 4, 3].length) (baseStart_862799 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_862799 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_862799 prefixEnd_862799 := by exact prefixLift 862799
  have htrace : WordTrace (prefixWord ++ tailWord_862799) baseStart_862799 baseEnd_862799 := by
    simpa [prefixWord, tailWord_862799, baseEnd_862799] using wordTrace_append hprefix tailTrace_862799
  have hstable : (prefixWord ++ tailWord_862799).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_862799).length < 2 ^ (prefixWord ++ tailWord_862799).sum := by decide
  have hdescent : baseEnd_862799 < baseStart_862799 := by decide
  rcases family_descends (prefixWord ++ tailWord_862799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_862802 : List Nat := [3, 2, 2, 1, 2, 1, 3, 4, 2]
def baseStart_862802 : Nat := 118140960795 + 862802 * 2 ^ 59
def prefixEnd_862802 : Nat := 4983230072969 + 3 ^ 40 * 862802 * 2
def baseEnd_862802 : Nat := 393806342809456459472935

theorem tailTrace_862802 : CollatzResearch.WordTrace tailWord_862802 prefixEnd_862802 393806342809456459472935 := by
  unfold tailWord_862802
  simp only [CollatzResearch.WordTrace]
  refine ⟨7867243555055795923797665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20979316146815455796793773 7867243555055795923797665)
  ·
    refine ⟨5900432666291846942848249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7867243555055795923797665 5900432666291846942848249)
    ·
      refine ⟨4425324499718885207136187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5900432666291846942848249 4425324499718885207136187)
      ·
        refine ⟨6637986749578327810704281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4425324499718885207136187 6637986749578327810704281)
        ·
          refine ⟨4978490062183745858028211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6637986749578327810704281 4978490062183745858028211)
          ·
            refine ⟨7467735093275618787042317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4978490062183745858028211 7467735093275618787042317)
            ·
              refine ⟨2800400659978357045140869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7467735093275618787042317 2800400659978357045140869)
              ·
                refine ⟨525075123745941945963913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2800400659978357045140869 525075123745941945963913)
                ·
                  refine ⟨393806342809456459472935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 525075123745941945963913 393806342809456459472935)
                  ·
                    rfl

theorem cell20_862802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 3, 4, 2].length) (baseStart_862802 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_862802 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_862802 prefixEnd_862802 := by exact prefixLift 862802
  have htrace : WordTrace (prefixWord ++ tailWord_862802) baseStart_862802 baseEnd_862802 := by
    simpa [prefixWord, tailWord_862802, baseEnd_862802] using wordTrace_append hprefix tailTrace_862802
  have hstable : (prefixWord ++ tailWord_862802).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_862802).length < 2 ^ (prefixWord ++ tailWord_862802).sum := by decide
  have hdescent : baseEnd_862802 < baseStart_862802 := by decide
  rcases family_descends (prefixWord ++ tailWord_862802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_862902 : List Nat := [5, 1, 3, 1, 2, 2, 6]
def baseStart_862902 : Nat := 118140960795 + 862902 * 2 ^ 59
def prefixEnd_862902 : Nat := 4983230072969 + 3 ^ 40 * 862902 * 2
def baseEnd_862902 : Nat := 43761331726033395126577

theorem tailTrace_862902 : CollatzResearch.WordTrace tailWord_862902 prefixEnd_862902 43761331726033395126577 := by
  unfold tailWord_862902
  simp only [CollatzResearch.WordTrace]
  refine ⟨1967038844991306298364435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20981747679907267182553973 1967038844991306298364435)
  ·
    refine ⟨2950558267486959447546653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1967038844991306298364435 2950558267486959447546653)
    ·
      refine ⟨1106459350307609792829995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2950558267486959447546653 1106459350307609792829995)
      ·
        refine ⟨1659689025461414689244993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1106459350307609792829995 1659689025461414689244993)
        ·
          refine ⟨1244766769096061016933745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1659689025461414689244993 1244766769096061016933745)
          ·
            refine ⟨933575076822045762700309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1244766769096061016933745 933575076822045762700309)
            ·
              refine ⟨43761331726033395126577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 933575076822045762700309 43761331726033395126577)
              ·
                rfl

theorem cell20_862902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 6].length) (baseStart_862902 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_862902 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_862902 prefixEnd_862902 := by exact prefixLift 862902
  have htrace : WordTrace (prefixWord ++ tailWord_862902) baseStart_862902 baseEnd_862902 := by
    simpa [prefixWord, tailWord_862902, baseEnd_862902] using wordTrace_append hprefix tailTrace_862902
  have hstable : (prefixWord ++ tailWord_862902).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_862902).length < 2 ^ (prefixWord ++ tailWord_862902).sum := by decide
  have hdescent : baseEnd_862902 < baseStart_862902 := by decide
  rcases family_descends (prefixWord ++ tailWord_862902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_862916 : List Nat := [2, 3, 3, 1, 1, 4, 1, 1, 4]
def baseStart_862916 : Nat := 118140960795 + 862916 * 2 ^ 59
def prefixEnd_862916 : Nat := 4983230072969 + 3 ^ 40 * 862916 * 2
def baseEnd_862916 : Nat := 393858375515778729672469

theorem tailTrace_862916 : CollatzResearch.WordTrace tailWord_862916 prefixEnd_862916 393858375515778729672469 := by
  unfold tailWord_862916
  simp only [CollatzResearch.WordTrace]
  refine ⟨15736566070905090582420301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20982088094540120776560401 15736566070905090582420301)
  ·
    refine ⟨5901212276589408968407613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15736566070905090582420301 5901212276589408968407613)
    ·
      refine ⟨2212954603721028363152855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5901212276589408968407613 2212954603721028363152855)
      ·
        refine ⟨3319431905581542544729283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2212954603721028363152855 3319431905581542544729283)
        ·
          refine ⟨4979147858372313817093925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3319431905581542544729283 4979147858372313817093925)
          ·
            refine ⟨933590223444808840705111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4979147858372313817093925 933590223444808840705111)
            ·
              refine ⟨1400385335167213261057667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 933590223444808840705111 1400385335167213261057667)
              ·
                refine ⟨2100578002750819891586501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1400385335167213261057667 2100578002750819891586501)
                ·
                  refine ⟨393858375515778729672469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2100578002750819891586501 393858375515778729672469)
                  ·
                    rfl

theorem cell20_862916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 1, 1, 4].length) (baseStart_862916 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_862916 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_862916 prefixEnd_862916 := by exact prefixLift 862916
  have htrace : WordTrace (prefixWord ++ tailWord_862916) baseStart_862916 baseEnd_862916 := by
    simpa [prefixWord, tailWord_862916, baseEnd_862916] using wordTrace_append hprefix tailTrace_862916
  have hstable : (prefixWord ++ tailWord_862916).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_862916).length < 2 ^ (prefixWord ++ tailWord_862916).sum := by decide
  have hdescent : baseEnd_862916 < baseStart_862916 := by decide
  rcases family_descends (prefixWord ++ tailWord_862916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_862999 : List Nat := [1, 1, 3, 4, 3, 1, 3, 4]
def baseStart_862999 : Nat := 118140960795 + 862999 * 2 ^ 59
def prefixEnd_862999 : Nat := 4983230072969 + 3 ^ 40 * 862999 * 2
def baseEnd_862999 : Nat := 131298752992466443301821

theorem tailTrace_862999 : CollatzResearch.WordTrace tailWord_862999 prefixEnd_862999 131298752992466443301821 := by
  unfold tailWord_862999
  simp only [CollatzResearch.WordTrace]
  refine ⟨31476159400509486340112051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20984106267006324226741367 31476159400509486340112051)
  ·
    refine ⟨47214239100764229510168077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31476159400509486340112051 47214239100764229510168077)
    ·
      refine ⟨17705339662786586066313029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47214239100764229510168077 17705339662786586066313029)
      ·
        refine ⟨3319751186772484887433693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17705339662786586066313029 3319751186772484887433693)
        ·
          refine ⟨1244906695039681832787635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3319751186772484887433693 1244906695039681832787635)
          ·
            refine ⟨1867360042559522749181453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1244906695039681832787635 1867360042559522749181453)
            ·
              refine ⟨700260015959821030943045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1867360042559522749181453 700260015959821030943045)
              ·
                refine ⟨131298752992466443301821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 700260015959821030943045 131298752992466443301821)
                ·
                  rfl

theorem cell20_862999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 3, 4].length) (baseStart_862999 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_862999 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_862999 prefixEnd_862999 := by exact prefixLift 862999
  have htrace : WordTrace (prefixWord ++ tailWord_862999) baseStart_862999 baseEnd_862999 := by
    simpa [prefixWord, tailWord_862999, baseEnd_862999] using wordTrace_append hprefix tailTrace_862999
  have hstable : (prefixWord ++ tailWord_862999).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_862999).length < 2 ^ (prefixWord ++ tailWord_862999).sum := by decide
  have hdescent : baseEnd_862999 < baseStart_862999 := by decide
  rcases family_descends (prefixWord ++ tailWord_862999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_863027 : List Nat := [1, 1, 1, 2, 6, 2, 1, 1, 5]
def baseStart_863027 : Nat := 118140960795 + 863027 * 2 ^ 59
def prefixEnd_863027 : Nat := 4983230072969 + 3 ^ 40 * 863027 * 2
def baseEnd_863027 : Nat := 393909038940355676972015

theorem tailTrace_863027 : CollatzResearch.WordTrace tailWord_863027 prefixEnd_863027 393909038940355676972015 := by
  unfold tailWord_863027
  simp only [CollatzResearch.WordTrace]
  refine ⟨31477180644408047122131335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20984787096272031414754223 31477180644408047122131335)
  ·
    refine ⟨47215770966612070683197003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31477180644408047122131335 47215770966612070683197003)
    ·
      refine ⟨70823656449918106024795505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47215770966612070683197003 70823656449918106024795505)
      ·
        refine ⟨53117742337438579518596629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70823656449918106024795505 53117742337438579518596629)
        ·
          refine ⟨2489894172067433414934217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 53117742337438579518596629 2489894172067433414934217)
          ·
            refine ⟨1867420629050575061200663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2489894172067433414934217 1867420629050575061200663)
            ·
              refine ⟨2801130943575862591800995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1867420629050575061200663 2801130943575862591800995)
              ·
                refine ⟨4201696415363793887701493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2801130943575862591800995 4201696415363793887701493)
                ·
                  refine ⟨393909038940355676972015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4201696415363793887701493 393909038940355676972015)
                  ·
                    rfl

theorem cell20_863027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 1, 1, 5].length) (baseStart_863027 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_863027 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_863027 prefixEnd_863027 := by exact prefixLift 863027
  have htrace : WordTrace (prefixWord ++ tailWord_863027) baseStart_863027 baseEnd_863027 := by
    simpa [prefixWord, tailWord_863027, baseEnd_863027] using wordTrace_append hprefix tailTrace_863027
  have hstable : (prefixWord ++ tailWord_863027).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_863027).length < 2 ^ (prefixWord ++ tailWord_863027).sum := by decide
  have hdescent : baseEnd_863027 < baseStart_863027 := by decide
  rcases family_descends (prefixWord ++ tailWord_863027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_863079 : List Nat := [1, 1, 5, 1, 2, 2, 8]
def baseStart_863079 : Nat := 118140960795 + 863079 * 2 ^ 59
def prefixEnd_863079 : Nat := 4983230072969 + 3 ^ 40 * 863079 * 2
def baseEnd_863079 : Nat := 43770308128586067470941

theorem tailTrace_863079 : CollatzResearch.WordTrace tailWord_863079 prefixEnd_863079 43770308128586067470941 := by
  unfold tailWord_863079
  simp only [CollatzResearch.WordTrace]
  refine ⟨31479077240219660003024291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20986051493479773335349527 31479077240219660003024291)
  ·
    refine ⟨47218615860329490004536437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31479077240219660003024291 47218615860329490004536437)
    ·
      refine ⟨4426745236905889687925291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 47218615860329490004536437 4426745236905889687925291)
      ·
        refine ⟨6640117855358834531887937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4426745236905889687925291 6640117855358834531887937)
        ·
          refine ⟨4980088391519125898915953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6640117855358834531887937 4980088391519125898915953)
          ·
            refine ⟨3735066293639344424186965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4980088391519125898915953 3735066293639344424186965)
            ·
              refine ⟨43770308128586067470941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3735066293639344424186965 43770308128586067470941)
              ·
                rfl

theorem cell20_863079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 8].length) (baseStart_863079 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_863079 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_863079 prefixEnd_863079 := by exact prefixLift 863079
  have htrace : WordTrace (prefixWord ++ tailWord_863079) baseStart_863079 baseEnd_863079 := by
    simpa [prefixWord, tailWord_863079, baseEnd_863079] using wordTrace_append hprefix tailTrace_863079
  have hstable : (prefixWord ++ tailWord_863079).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_863079).length < 2 ^ (prefixWord ++ tailWord_863079).sum := by decide
  have hdescent : baseEnd_863079 < baseStart_863079 := by decide
  rcases family_descends (prefixWord ++ tailWord_863079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_863089 : List Nat := [1, 2, 2, 2, 1, 6, 1, 1, 4]
def baseStart_863089 : Nat := 118140960795 + 863089 * 2 ^ 59
def prefixEnd_863089 : Nat := 4983230072969 + 3 ^ 40 * 863089 * 2
def baseEnd_863089 : Nat := 393937337429759016905095

theorem tailTrace_863089 : CollatzResearch.WordTrace tailWord_863089 prefixEnd_863089 393937337429759016905095 := by
  unfold tailWord_863089
  simp only [CollatzResearch.WordTrace]
  refine ⟨31479441970183431710888321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20986294646788954473925547 31479441970183431710888321)
  ·
    refine ⟨23609581477637573783166241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31479441970183431710888321 23609581477637573783166241)
    ·
      refine ⟨17707186108228180337374681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23609581477637573783166241 17707186108228180337374681)
      ·
        refine ⟨13280389581171135253031011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17707186108228180337374681 13280389581171135253031011)
        ·
          refine ⟨19920584371756702879546517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13280389581171135253031011 19920584371756702879546517)
          ·
            refine ⟨933777392426095447478743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 19920584371756702879546517 933777392426095447478743)
            ·
              refine ⟨1400666088639143171218115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 933777392426095447478743 1400666088639143171218115)
              ·
                refine ⟨2100999132958714756827173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1400666088639143171218115 2100999132958714756827173)
                ·
                  refine ⟨393937337429759016905095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2100999132958714756827173 393937337429759016905095)
                  ·
                    rfl

theorem cell20_863089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 1, 1, 4].length) (baseStart_863089 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_863089 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_863089 prefixEnd_863089 := by exact prefixLift 863089
  have htrace : WordTrace (prefixWord ++ tailWord_863089) baseStart_863089 baseEnd_863089 := by
    simpa [prefixWord, tailWord_863089, baseEnd_863089] using wordTrace_append hprefix tailTrace_863089
  have hstable : (prefixWord ++ tailWord_863089).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_863089).length < 2 ^ (prefixWord ++ tailWord_863089).sum := by decide
  have hdescent : baseEnd_863089 < baseStart_863089 := by decide
  rcases family_descends (prefixWord ++ tailWord_863089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_863127 : List Nat := [1, 1, 3, 3, 1, 2, 2, 5, 2]
def baseStart_863127 : Nat := 118140960795 + 863127 * 2 ^ 59
def prefixEnd_863127 : Nat := 4983230072969 + 3 ^ 40 * 863127 * 2
def baseEnd_863127 : Nat := 393954681665199773638273

theorem tailTrace_863127 : CollatzResearch.WordTrace tailWord_863127 prefixEnd_863127 393954681665199773638273 := by
  unfold tailWord_863127
  simp only [CollatzResearch.WordTrace]
  refine ⟨31480827944045764200771635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20987218629363842800514423 31480827944045764200771635)
  ·
    refine ⟨47221241916068646301157453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31480827944045764200771635 47221241916068646301157453)
    ·
      refine ⟨17707965718525742362934045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47221241916068646301157453 17707965718525742362934045)
      ·
        refine ⟨6640487144447153386100267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17707965718525742362934045 6640487144447153386100267)
        ·
          refine ⟨9960730716670730079150401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6640487144447153386100267 9960730716670730079150401)
          ·
            refine ⟨7470548037503047559362801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9960730716670730079150401 7470548037503047559362801)
            ·
              refine ⟨5602911028127285669522101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7470548037503047559362801 5602911028127285669522101)
              ·
                refine ⟨525272908886933031517697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5602911028127285669522101 525272908886933031517697)
                ·
                  refine ⟨393954681665199773638273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 525272908886933031517697 393954681665199773638273)
                  ·
                    rfl

theorem cell20_863127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 5, 2].length) (baseStart_863127 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_863127 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_863127 prefixEnd_863127 := by exact prefixLift 863127
  have htrace : WordTrace (prefixWord ++ tailWord_863127) baseStart_863127 baseEnd_863127 := by
    simpa [prefixWord, tailWord_863127, baseEnd_863127] using wordTrace_append hprefix tailTrace_863127
  have hstable : (prefixWord ++ tailWord_863127).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_863127).length < 2 ^ (prefixWord ++ tailWord_863127).sum := by decide
  have hdescent : baseEnd_863127 < baseStart_863127 := by decide
  rcases family_descends (prefixWord ++ tailWord_863127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_863165 : List Nat := [1, 4, 1, 2, 4, 1, 1, 2, 4]
def baseStart_863165 : Nat := 118140960795 + 863165 * 2 ^ 59
def prefixEnd_863165 : Nat := 4983230072969 + 3 ^ 40 * 863165 * 2
def baseEnd_863165 : Nat := 393972025900640530371451

theorem tailTrace_863165 : CollatzResearch.WordTrace tailWord_863165 prefixEnd_863165 393972025900640530371451 := by
  unfold tailWord_863165
  simp only [CollatzResearch.WordTrace]
  refine ⟨31482213917908096690654949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20988142611938731127103299 31482213917908096690654949)
  ·
    refine ⟨5902915109607768129497803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31482213917908096690654949 5902915109607768129497803)
    ·
      refine ⟨8854372664411652194246705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5902915109607768129497803 8854372664411652194246705)
      ·
        refine ⟨6640779498308739145685029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8854372664411652194246705 6640779498308739145685029)
        ·
          refine ⟨1245146155932888589815943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6640779498308739145685029 1245146155932888589815943)
          ·
            refine ⟨1867719233899332884723915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1245146155932888589815943 1867719233899332884723915)
            ·
              refine ⟨2801578850848999327085873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1867719233899332884723915 2801578850848999327085873)
              ·
                refine ⟨2101184138136749495314405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2801578850848999327085873 2101184138136749495314405)
                ·
                  refine ⟨393972025900640530371451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2101184138136749495314405 393972025900640530371451)
                  ·
                    rfl

theorem cell20_863165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 1, 2, 4].length) (baseStart_863165 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_863165 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_863165 prefixEnd_863165 := by exact prefixLift 863165
  have htrace : WordTrace (prefixWord ++ tailWord_863165) baseStart_863165 baseEnd_863165 := by
    simpa [prefixWord, tailWord_863165, baseEnd_863165] using wordTrace_append hprefix tailTrace_863165
  have hstable : (prefixWord ++ tailWord_863165).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_863165).length < 2 ^ (prefixWord ++ tailWord_863165).sum := by decide
  have hdescent : baseEnd_863165 < baseStart_863165 := by decide
  rcases family_descends (prefixWord ++ tailWord_863165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_863174 : List Nat := [6, 1, 3, 1, 1, 1, 2, 3, 2]
def baseStart_863174 : Nat := 118140960795 + 863174 * 2 ^ 59
def prefixEnd_863174 : Nat := 4983230072969 + 3 ^ 40 * 863174 * 2
def baseEnd_863174 : Nat := 393976133745876499071415

theorem tailTrace_863174 : CollatzResearch.WordTrace tailWord_863174 prefixEnd_863174 393976133745876499071415 := by
  unfold tailWord_863174
  simp only [CollatzResearch.WordTrace]
  refine ⟨983829442964859100866643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 20988361449916994151821717 983829442964859100866643)
  ·
    refine ⟨1475744164447288651299965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 983829442964859100866643 1475744164447288651299965)
    ·
      refine ⟨553404061667733244237487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1475744164447288651299965 553404061667733244237487)
      ·
        refine ⟨830106092501599866356231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 553404061667733244237487 830106092501599866356231)
        ·
          refine ⟨1245159138752399799534347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 830106092501599866356231 1245159138752399799534347)
          ·
            refine ⟨1867738708128599699301521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1245159138752399799534347 1867738708128599699301521)
            ·
              refine ⟨1400804031096449774476141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1867738708128599699301521 1400804031096449774476141)
              ·
                refine ⟨525301511661168665428553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1400804031096449774476141 525301511661168665428553)
                ·
                  refine ⟨393976133745876499071415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 525301511661168665428553 393976133745876499071415)
                  ·
                    rfl

theorem cell20_863174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 2, 3, 2].length) (baseStart_863174 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_863174 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_863174 prefixEnd_863174 := by exact prefixLift 863174
  have htrace : WordTrace (prefixWord ++ tailWord_863174) baseStart_863174 baseEnd_863174 := by
    simpa [prefixWord, tailWord_863174, baseEnd_863174] using wordTrace_append hprefix tailTrace_863174
  have hstable : (prefixWord ++ tailWord_863174).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_863174).length < 2 ^ (prefixWord ++ tailWord_863174).sum := by decide
  have hdescent : baseEnd_863174 < baseStart_863174 := by decide
  rcases family_descends (prefixWord ++ tailWord_863174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_863182 : List Nat := [4, 1, 1, 1, 2, 4, 2, 3, 2]
def baseStart_863182 : Nat := 118140960795 + 863182 * 2 ^ 59
def prefixEnd_863182 : Nat := 4983230072969 + 3 ^ 40 * 863182 * 2
def baseEnd_863182 : Nat := 393979785163864026804715

theorem tailTrace_863182 : CollatzResearch.WordTrace tailWord_863182 prefixEnd_863182 393979785163864026804715 := by
  unfold tailWord_863182
  simp only [CollatzResearch.WordTrace]
  refine ⟨3935354244855813574252975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20988555972564339062682533 3935354244855813574252975)
  ·
    refine ⟨5903031367283720361379463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3935354244855813574252975 5903031367283720361379463)
    ·
      refine ⟨8854547050925580542069195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5903031367283720361379463 8854547050925580542069195)
      ·
        refine ⟨13281820576388370813103793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8854547050925580542069195 13281820576388370813103793)
        ·
          refine ⟨9961365432291278109827845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13281820576388370813103793 9961365432291278109827845)
          ·
            refine ⟨1867756018554614645592721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9961365432291278109827845 1867756018554614645592721)
            ·
              refine ⟨1400817013915960984194541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1867756018554614645592721 1400817013915960984194541)
              ·
                refine ⟨525306380218485369072953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1400817013915960984194541 525306380218485369072953)
                ·
                  refine ⟨393979785163864026804715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 525306380218485369072953 393979785163864026804715)
                  ·
                    rfl

theorem cell20_863182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 2, 3, 2].length) (baseStart_863182 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_863182 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_863182 prefixEnd_863182 := by exact prefixLift 863182
  have htrace : WordTrace (prefixWord ++ tailWord_863182) baseStart_863182 baseEnd_863182 := by
    simpa [prefixWord, tailWord_863182, baseEnd_863182] using wordTrace_append hprefix tailTrace_863182
  have hstable : (prefixWord ++ tailWord_863182).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_863182).length < 2 ^ (prefixWord ++ tailWord_863182).sum := by decide
  have hdescent : baseEnd_863182 < baseStart_863182 := by decide
  rcases family_descends (prefixWord ++ tailWord_863182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_863193 : List Nat := [1, 2, 1, 2, 5, 2, 7]
def baseStart_863193 : Nat := 118140960795 + 863193 * 2 ^ 59
def prefixEnd_863193 : Nat := 4983230072969 + 3 ^ 40 * 863193 * 2
def baseEnd_863193 : Nat := 43776089540399653048667

theorem tailTrace_863193 : CollatzResearch.WordTrace tailWord_863193 prefixEnd_863193 43776089540399653048667 := by
  unfold tailWord_863193
  simp only [CollatzResearch.WordTrace]
  refine ⟨31483235161806657472674233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20988823441204438315116155 31483235161806657472674233)
  ·
    refine ⟨23612426371354993104505675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31483235161806657472674233 23612426371354993104505675)
    ·
      refine ⟨35418639557032489656758513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23612426371354993104505675 35418639557032489656758513)
      ·
        refine ⟨26563979667774367242568885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35418639557032489656758513 26563979667774367242568885)
        ·
          refine ⟨2490373093853846928990833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26563979667774367242568885 2490373093853846928990833)
          ·
            refine ⟨1867779820390385196743125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2490373093853846928990833 1867779820390385196743125)
            ·
              refine ⟨43776089540399653048667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1867779820390385196743125 43776089540399653048667)
              ·
                rfl

theorem cell20_863193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 7].length) (baseStart_863193 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_863193 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_863193 prefixEnd_863193 := by exact prefixLift 863193
  have htrace : WordTrace (prefixWord ++ tailWord_863193) baseStart_863193 baseEnd_863193 := by
    simpa [prefixWord, tailWord_863193, baseEnd_863193] using wordTrace_append hprefix tailTrace_863193
  have hstable : (prefixWord ++ tailWord_863193).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_863193).length < 2 ^ (prefixWord ++ tailWord_863193).sum := by decide
  have hdescent : baseEnd_863193 < baseStart_863193 := by decide
  rcases family_descends (prefixWord ++ tailWord_863193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_863203 : List Nat := [1, 1, 1, 6, 1, 1, 1, 6, 2]
def baseStart_863203 : Nat := 118140960795 + 863203 * 2 ^ 59
def prefixEnd_863203 : Nat := 4983230072969 + 3 ^ 40 * 863203 * 2
def baseEnd_863203 : Nat := 393989370136081287104629

theorem tailTrace_863203 : CollatzResearch.WordTrace tailWord_863203 prefixEnd_863203 393989370136081287104629 := by
  unfold tailWord_863203
  simp only [CollatzResearch.WordTrace]
  refine ⟨31483599891770429180538263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20989066594513619453692175 31483599891770429180538263)
  ·
    refine ⟨47225399837655643770807395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31483599891770429180538263 47225399837655643770807395)
    ·
      refine ⟨70838099756483465656211093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47225399837655643770807395 70838099756483465656211093)
      ·
        refine ⟨3320535926085162452634895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 70838099756483465656211093 3320535926085162452634895)
        ·
          refine ⟨4980803889127743678952343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3320535926085162452634895 4980803889127743678952343)
          ·
            refine ⟨7471205833691615518428515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4980803889127743678952343 7471205833691615518428515)
            ·
              refine ⟨11206808750537423277642773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7471205833691615518428515 11206808750537423277642773)
              ·
                refine ⟨525319160181441716139505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 11206808750537423277642773 525319160181441716139505)
                ·
                  refine ⟨393989370136081287104629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 525319160181441716139505 393989370136081287104629)
                  ·
                    rfl

theorem cell20_863203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 6, 2].length) (baseStart_863203 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_863203 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_863203 prefixEnd_863203 := by exact prefixLift 863203
  have htrace : WordTrace (prefixWord ++ tailWord_863203) baseStart_863203 baseEnd_863203 := by
    simpa [prefixWord, tailWord_863203, baseEnd_863203] using wordTrace_append hprefix tailTrace_863203
  have hstable : (prefixWord ++ tailWord_863203).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_863203).length < 2 ^ (prefixWord ++ tailWord_863203).sum := by decide
  have hdescent : baseEnd_863203 < baseStart_863203 := by decide
  rcases family_descends (prefixWord ++ tailWord_863203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_863255 : List Nat := [1, 1, 3, 5, 1, 1, 2, 1, 5]
def baseStart_863255 : Nat := 118140960795 + 863255 * 2 ^ 59
def prefixEnd_863255 : Nat := 4983230072969 + 3 ^ 40 * 863255 * 2
def baseEnd_863255 : Nat := 394013104353000217371083

theorem tailTrace_863255 : CollatzResearch.WordTrace tailWord_863255 prefixEnd_863255 394013104353000217371083 := by
  unfold tailWord_863255
  simp only [CollatzResearch.WordTrace]
  refine ⟨31485496487582042061431219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20990330991721361374287479 31485496487582042061431219)
  ·
    refine ⟨47228244731373063092146829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31485496487582042061431219 47228244731373063092146829)
    ·
      refine ⟨17710591774264898659555061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47228244731373063092146829 17710591774264898659555061)
      ·
        refine ⟨1660367978837334249333287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 17710591774264898659555061 1660367978837334249333287)
        ·
          refine ⟨2490551968256001373999931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1660367978837334249333287 2490551968256001373999931)
          ·
            refine ⟨3735827952384002060999897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2490551968256001373999931 3735827952384002060999897)
            ·
              refine ⟨2801870964288001545749923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3735827952384002060999897 2801870964288001545749923)
              ·
                refine ⟨4202806446432002318624885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2801870964288001545749923 4202806446432002318624885)
                ·
                  refine ⟨394013104353000217371083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4202806446432002318624885 394013104353000217371083)
                  ·
                    rfl

theorem cell20_863255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 2, 1, 5].length) (baseStart_863255 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_863255 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_863255 prefixEnd_863255 := by exact prefixLift 863255
  have htrace : WordTrace (prefixWord ++ tailWord_863255) baseStart_863255 baseEnd_863255 := by
    simpa [prefixWord, tailWord_863255, baseEnd_863255] using wordTrace_append hprefix tailTrace_863255
  have hstable : (prefixWord ++ tailWord_863255).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_863255).length < 2 ^ (prefixWord ++ tailWord_863255).sum := by decide
  have hdescent : baseEnd_863255 < baseStart_863255 := by decide
  rcases family_descends (prefixWord ++ tailWord_863255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_863258 : List Nat := [3, 1, 1, 3, 1, 2, 5, 2, 2]
def baseStart_863258 : Nat := 118140960795 + 863258 * 2 ^ 59
def prefixEnd_863258 : Nat := 4983230072969 + 3 ^ 40 * 863258 * 2
def baseEnd_863258 : Nat := 394014473634745540271071

theorem tailTrace_863258 : CollatzResearch.WordTrace tailWord_863258 prefixEnd_863258 394014473634745540271071 := by
  unfold tailWord_863258
  simp only [CollatzResearch.WordTrace]
  refine ⟨7871401476642793393447607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20990403937714115715860285 7871401476642793393447607)
  ·
    refine ⟨11807102214964190090171411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7871401476642793393447607 11807102214964190090171411)
    ·
      refine ⟨17710653322446285135257117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11807102214964190090171411 17710653322446285135257117)
      ·
        refine ⟨6641494995917356925721419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17710653322446285135257117 6641494995917356925721419)
        ·
          refine ⟨9962242493876035388582129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6641494995917356925721419 9962242493876035388582129)
          ·
            refine ⟨7471681870407026541436597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9962242493876035388582129 7471681870407026541436597)
            ·
              refine ⟨700470175350658738259681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7471681870407026541436597 700470175350658738259681)
              ·
                refine ⟨525352631512994053694761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 700470175350658738259681 525352631512994053694761)
                ·
                  refine ⟨394014473634745540271071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 525352631512994053694761 394014473634745540271071)
                  ·
                    rfl

theorem cell20_863258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 5, 2, 2].length) (baseStart_863258 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_863258 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_863258 prefixEnd_863258 := by exact prefixLift 863258
  have htrace : WordTrace (prefixWord ++ tailWord_863258) baseStart_863258 baseEnd_863258 := by
    simpa [prefixWord, tailWord_863258, baseEnd_863258] using wordTrace_append hprefix tailTrace_863258
  have hstable : (prefixWord ++ tailWord_863258).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_863258).length < 2 ^ (prefixWord ++ tailWord_863258).sum := by decide
  have hdescent : baseEnd_863258 < baseStart_863258 := by decide
  rcases family_descends (prefixWord ++ tailWord_863258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_863269 : List Nat := [1, 3, 1, 2, 2, 2, 4, 5]
def baseStart_863269 : Nat := 118140960795 + 863269 * 2 ^ 59
def prefixEnd_863269 : Nat := 4983230072969 + 3 ^ 40 * 863269 * 2
def baseEnd_863269 : Nat := 131339831444826130301453

theorem tailTrace_863269 : CollatzResearch.WordTrace tailWord_863269 prefixEnd_863269 131339831444826130301453 := by
  unfold tailWord_863269
  simp only [CollatzResearch.WordTrace]
  refine ⟨31486007109531322452440861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20990671406354214968293907 31486007109531322452440861)
  ·
    refine ⟨11807252666074245919665323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31486007109531322452440861 11807252666074245919665323)
    ·
      refine ⟨17710878999111368879497985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11807252666074245919665323 17710878999111368879497985)
      ·
        refine ⟨13283159249333526659623489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17710878999111368879497985 13283159249333526659623489)
        ·
          refine ⟨9962369437000144994717617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13283159249333526659623489 9962369437000144994717617)
          ·
            refine ⟨7471777077750108746038213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9962369437000144994717617 7471777077750108746038213)
            ·
              refine ⟨1400958202078145389882165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7471777077750108746038213 1400958202078145389882165)
              ·
                refine ⟨131339831444826130301453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1400958202078145389882165 131339831444826130301453)
                ·
                  rfl

theorem cell20_863269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 4, 5].length) (baseStart_863269 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_863269 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_863269 prefixEnd_863269 := by exact prefixLift 863269
  have htrace : WordTrace (prefixWord ++ tailWord_863269) baseStart_863269 baseEnd_863269 := by
    simpa [prefixWord, tailWord_863269, baseEnd_863269] using wordTrace_append hprefix tailTrace_863269
  have hstable : (prefixWord ++ tailWord_863269).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_863269).length < 2 ^ (prefixWord ++ tailWord_863269).sum := by decide
  have hdescent : baseEnd_863269 < baseStart_863269 := by decide
  rcases family_descends (prefixWord ++ tailWord_863269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_863283 : List Nat := [1, 1, 1, 2, 4, 1, 1, 3, 6]
def baseStart_863283 : Nat := 118140960795 + 863283 * 2 ^ 59
def prefixEnd_863283 : Nat := 4983230072969 + 3 ^ 40 * 863283 * 2
def baseEnd_863283 : Nat := 394025884315956564437635

theorem tailTrace_863283 : CollatzResearch.WordTrace tailWord_863283 prefixEnd_863283 394025884315956564437635 := by
  unfold tailWord_863283
  simp only [CollatzResearch.WordTrace]
  refine ⟨31486517731480602843450503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20991011820987068562300335 31486517731480602843450503)
  ·
    refine ⟨47229776597220904265175755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31486517731480602843450503 47229776597220904265175755)
    ·
      refine ⟨70844664895831356397763633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47229776597220904265175755 70844664895831356397763633)
      ·
        refine ⟨53133498671873517298322725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70844664895831356397763633 53133498671873517298322725)
        ·
          refine ⟨9962531000976284493435511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53133498671873517298322725 9962531000976284493435511)
          ·
            refine ⟨14943796501464426740153267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9962531000976284493435511 14943796501464426740153267)
            ·
              refine ⟨22415694752196640110229901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14943796501464426740153267 22415694752196640110229901)
              ·
                refine ⟨8405885532073740041336213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22415694752196640110229901 8405885532073740041336213)
                ·
                  refine ⟨394025884315956564437635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8405885532073740041336213 394025884315956564437635)
                  ·
                    rfl

theorem cell20_863283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 3, 6].length) (baseStart_863283 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_863283 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_863283 prefixEnd_863283 := by exact prefixLift 863283
  have htrace : WordTrace (prefixWord ++ tailWord_863283) baseStart_863283 baseEnd_863283 := by
    simpa [prefixWord, tailWord_863283, baseEnd_863283] using wordTrace_append hprefix tailTrace_863283
  have hstable : (prefixWord ++ tailWord_863283).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_863283).length < 2 ^ (prefixWord ++ tailWord_863283).sum := by decide
  have hdescent : baseEnd_863283 < baseStart_863283 := by decide
  rcases family_descends (prefixWord ++ tailWord_863283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_863286 : List Nat := [5, 1, 2, 1, 1, 2, 2, 6]
def baseStart_863286 : Nat := 118140960795 + 863286 * 2 ^ 59
def prefixEnd_863286 : Nat := 4983230072969 + 3 ^ 40 * 863286 * 2
def baseEnd_863286 : Nat := 131342417865900629112541

theorem tailTrace_863286 : CollatzResearch.WordTrace tailWord_863286 prefixEnd_863286 131342417865900629112541 := by
  unfold tailWord_863286
  simp only [CollatzResearch.WordTrace]
  refine ⟨1967914196904358397238107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20991084766979822903873141 1967914196904358397238107)
  ·
    refine ⟨2951871295356537595857161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1967914196904358397238107 2951871295356537595857161)
    ·
      refine ⟨2213903471517403196892871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2951871295356537595857161 2213903471517403196892871)
      ·
        refine ⟨3320855207276104795339307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2213903471517403196892871 3320855207276104795339307)
        ·
          refine ⟨4981282810914157193008961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3320855207276104795339307 4981282810914157193008961)
          ·
            refine ⟨3735962108185617894756721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4981282810914157193008961 3735962108185617894756721)
            ·
              refine ⟨2801971581139213421067541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3735962108185617894756721 2801971581139213421067541)
              ·
                refine ⟨131342417865900629112541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2801971581139213421067541 131342417865900629112541)
                ·
                  rfl

theorem cell20_863286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 2, 6].length) (baseStart_863286 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_863286 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_863286 prefixEnd_863286 := by exact prefixLift 863286
  have htrace : WordTrace (prefixWord ++ tailWord_863286) baseStart_863286 baseEnd_863286 := by
    simpa [prefixWord, tailWord_863286, baseEnd_863286] using wordTrace_append hprefix tailTrace_863286
  have hstable : (prefixWord ++ tailWord_863286).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_863286).length < 2 ^ (prefixWord ++ tailWord_863286).sum := by decide
  have hdescent : baseEnd_863286 < baseStart_863286 := by decide
  rcases family_descends (prefixWord ++ tailWord_863286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_863317 : List Nat := [1, 3, 2, 2, 1, 2, 3, 4, 2]
def baseStart_863317 : Nat := 118140960795 + 863317 * 2 ^ 59
def prefixEnd_863317 : Nat := 4983230072969 + 3 ^ 40 * 863317 * 2
def baseEnd_863317 : Nat := 394041402842403557304163

theorem tailTrace_863317 : CollatzResearch.WordTrace tailWord_863317 prefixEnd_863317 394041402842403557304163 := by
  unfold tailWord_863317
  simp only [CollatzResearch.WordTrace]
  refine ⟨31487757813357426650188205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20991838542238284433458803 31487757813357426650188205)
  ·
    refine ⟨11807909180009034993820577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31487757813357426650188205 11807909180009034993820577)
    ·
      refine ⟨8855931885006776245365433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11807909180009034993820577 8855931885006776245365433)
      ·
        refine ⟨6641948913755082184024075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8855931885006776245365433 6641948913755082184024075)
        ·
          refine ⟨9962923370632623276036113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6641948913755082184024075 9962923370632623276036113)
          ·
            refine ⟨7472192527974467457027085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9962923370632623276036113 7472192527974467457027085)
            ·
              refine ⟨2802072197990425296385157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7472192527974467457027085 2802072197990425296385157)
              ·
                refine ⟨525388537123204743072217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2802072197990425296385157 525388537123204743072217)
                ·
                  refine ⟨394041402842403557304163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 525388537123204743072217 394041402842403557304163)
                  ·
                    rfl

theorem cell20_863317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 3, 4, 2].length) (baseStart_863317 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_863317 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_863317 prefixEnd_863317 := by exact prefixLift 863317
  have htrace : WordTrace (prefixWord ++ tailWord_863317) baseStart_863317 baseEnd_863317 := by
    simpa [prefixWord, tailWord_863317, baseEnd_863317] using wordTrace_append hprefix tailTrace_863317
  have hstable : (prefixWord ++ tailWord_863317).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_863317).length < 2 ^ (prefixWord ++ tailWord_863317).sum := by decide
  have hdescent : baseEnd_863317 < baseStart_863317 := by decide
  rcases family_descends (prefixWord ++ tailWord_863317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_863338 : List Nat := [3, 1, 3, 2, 2, 1, 1, 1, 6]
def baseStart_863338 : Nat := 118140960795 + 863338 * 2 ^ 59
def prefixEnd_863338 : Nat := 4983230072969 + 3 ^ 40 * 863338 * 2
def baseEnd_863338 : Nat := 394050987814620817604077

theorem tailTrace_863338 : CollatzResearch.WordTrace tailWord_863338 prefixEnd_863338 394050987814620817604077 := by
  unfold tailWord_863338
  simp only [CollatzResearch.WordTrace]
  refine ⟨7872130936570336809175667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20992349164187564824468445 7872130936570336809175667)
  ·
    refine ⟨11808196404855505213763501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7872130936570336809175667 11808196404855505213763501)
    ·
      refine ⟨4428073651820814455161313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11808196404855505213763501 4428073651820814455161313)
      ·
        refine ⟨3321055238865610841370985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4428073651820814455161313 3321055238865610841370985)
        ·
          refine ⟨2490791429149208131028239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3321055238865610841370985 2490791429149208131028239)
          ·
            refine ⟨3736187143723812196542359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2490791429149208131028239 3736187143723812196542359)
            ·
              refine ⟨5604280715585718294813539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3736187143723812196542359 5604280715585718294813539)
              ·
                refine ⟨8406421073378577442220309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5604280715585718294813539 8406421073378577442220309)
                ·
                  refine ⟨394050987814620817604077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8406421073378577442220309 394050987814620817604077)
                  ·
                    rfl

theorem cell20_863338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 1, 6].length) (baseStart_863338 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_863338 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_863338 prefixEnd_863338 := by exact prefixLift 863338
  have htrace : WordTrace (prefixWord ++ tailWord_863338) baseStart_863338 baseEnd_863338 := by
    simpa [prefixWord, tailWord_863338, baseEnd_863338] using wordTrace_append hprefix tailTrace_863338
  have hstable : (prefixWord ++ tailWord_863338).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_863338).length < 2 ^ (prefixWord ++ tailWord_863338).sum := by decide
  have hdescent : baseEnd_863338 < baseStart_863338 := by decide
  rcases family_descends (prefixWord ++ tailWord_863338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_863358 : List Nat := [4, 2, 4, 1, 1, 1, 7]
def baseStart_863358 : Nat := 118140960795 + 863358 * 2 ^ 59
def prefixEnd_863358 : Nat := 4983230072969 + 3 ^ 40 * 863358 * 2
def baseEnd_863358 : Nat := 43784457373287737437481

theorem tailTrace_863358 : CollatzResearch.WordTrace tailWord_863358 prefixEnd_863358 43784457373287737437481 := by
  unfold tailWord_863358
  simp only [CollatzResearch.WordTrace]
  refine ⟨3936156650776111331553841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20992835470805927101620485 3936156650776111331553841)
  ·
    refine ⟨2952117488082083498665381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3936156650776111331553841 2952117488082083498665381)
    ·
      refine ⟨553522029015390655999759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2952117488082083498665381 553522029015390655999759)
      ·
        refine ⟨830283043523085983999639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 553522029015390655999759 830283043523085983999639)
        ·
          refine ⟨1245424565284628975999459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 830283043523085983999639 1245424565284628975999459)
          ·
            refine ⟨1868136847926943463999189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1245424565284628975999459 1868136847926943463999189)
            ·
              refine ⟨43784457373287737437481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1868136847926943463999189 43784457373287737437481)
              ·
                rfl

theorem cell20_863358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 7].length) (baseStart_863358 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_863358 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_863358 prefixEnd_863358 := by exact prefixLift 863358
  have htrace : WordTrace (prefixWord ++ tailWord_863358) baseStart_863358 baseEnd_863358 := by
    simpa [prefixWord, tailWord_863358, baseEnd_863358] using wordTrace_append hprefix tailTrace_863358
  have hstable : (prefixWord ++ tailWord_863358).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_863358).length < 2 ^ (prefixWord ++ tailWord_863358).sum := by decide
  have hdescent : baseEnd_863358 < baseStart_863358 := by decide
  rcases family_descends (prefixWord ++ tailWord_863358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_863365 : List Nat := [1, 3, 1, 1, 7, 1, 1, 2, 3]
def baseStart_863365 : Nat := 118140960795 + 863365 * 2 ^ 59
def prefixEnd_863365 : Nat := 4983230072969 + 3 ^ 40 * 863365 * 2
def baseEnd_863365 : Nat := 394063311350328723703967

theorem tailTrace_863365 : CollatzResearch.WordTrace tailWord_863365 prefixEnd_863365 394063311350328723703967 := by
  unfold tailWord_863365
  simp only [CollatzResearch.WordTrace]
  refine ⟨31489508517183530847935549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20993005678122353898623699 31489508517183530847935549)
  ·
    refine ⟨11808565693943824067975831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31489508517183530847935549 11808565693943824067975831)
    ·
      refine ⟨17712848540915736101963747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11808565693943824067975831 17712848540915736101963747)
      ·
        refine ⟨26569272811373604152945621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17712848540915736101963747 26569272811373604152945621)
        ·
          refine ⟨622717331516568847334663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 26569272811373604152945621 622717331516568847334663)
          ·
            refine ⟨934075997274853271001995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 622717331516568847334663 934075997274853271001995)
            ·
              refine ⟨1401113995912279906502993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 934075997274853271001995 1401113995912279906502993)
              ·
                refine ⟨1050835496934209929877245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1401113995912279906502993 1050835496934209929877245)
                ·
                  refine ⟨394063311350328723703967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1050835496934209929877245 394063311350328723703967)
                  ·
                    rfl

theorem cell20_863365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 1, 2, 3].length) (baseStart_863365 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_863365 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_863365 prefixEnd_863365 := by exact prefixLift 863365
  have htrace : WordTrace (prefixWord ++ tailWord_863365) baseStart_863365 baseEnd_863365 := by
    simpa [prefixWord, tailWord_863365, baseEnd_863365] using wordTrace_append hprefix tailTrace_863365
  have hstable : (prefixWord ++ tailWord_863365).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_863365).length < 2 ^ (prefixWord ++ tailWord_863365).sum := by decide
  have hdescent : baseEnd_863365 < baseStart_863365 := by decide
  rcases family_descends (prefixWord ++ tailWord_863365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_863369 : List Nat := [1, 2, 1, 1, 4, 3, 3, 2, 3]
def baseStart_863369 : Nat := 118140960795 + 863369 * 2 ^ 59
def prefixEnd_863369 : Nat := 4983230072969 + 3 ^ 40 * 863369 * 2
def baseEnd_863369 : Nat := 394065137059322487570617

theorem tailTrace_863369 : CollatzResearch.WordTrace tailWord_863369 prefixEnd_863369 394065137059322487570617 := by
  unfold tailWord_863369
  simp only [CollatzResearch.WordTrace]
  refine ⟨31489654409169039531081161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20993102939446026354054107 31489654409169039531081161)
  ·
    refine ⟨23617240806876779648310871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31489654409169039531081161 23617240806876779648310871)
    ·
      refine ⟨35425861210315169472466307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23617240806876779648310871 35425861210315169472466307)
      ·
        refine ⟨53138791815472754208699461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35425861210315169472466307 53138791815472754208699461)
        ·
          refine ⟨9963523465401141414131149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53138791815472754208699461 9963523465401141414131149)
          ·
            refine ⟨3736321299525428030299181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9963523465401141414131149 3736321299525428030299181)
            ·
              refine ⟨1401120487322035511362193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3736321299525428030299181 1401120487322035511362193)
              ·
                refine ⟨1050840365491526633521645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1401120487322035511362193 1050840365491526633521645)
                ·
                  refine ⟨394065137059322487570617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1050840365491526633521645 394065137059322487570617)
                  ·
                    rfl

theorem cell20_863369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 3, 2, 3].length) (baseStart_863369 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_863369 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_863369 prefixEnd_863369 := by exact prefixLift 863369
  have htrace : WordTrace (prefixWord ++ tailWord_863369) baseStart_863369 baseEnd_863369 := by
    simpa [prefixWord, tailWord_863369, baseEnd_863369] using wordTrace_append hprefix tailTrace_863369
  have hstable : (prefixWord ++ tailWord_863369).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_863369).length < 2 ^ (prefixWord ++ tailWord_863369).sum := by decide
  have hdescent : baseEnd_863369 < baseStart_863369 := by decide
  rcases family_descends (prefixWord ++ tailWord_863369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_863410 : List Nat := [3, 2, 1, 1, 1, 6, 1, 3, 2]
def baseStart_863410 : Nat := 118140960795 + 863410 * 2 ^ 59
def prefixEnd_863410 : Nat := 4983230072969 + 3 ^ 40 * 863410 * 2
def baseEnd_863410 : Nat := 394083850576508567203783

theorem tailTrace_863410 : CollatzResearch.WordTrace tailWord_863410 prefixEnd_863410 394083850576508567203783 := by
  unfold tailWord_863410
  simp only [CollatzResearch.WordTrace]
  refine ⟨7872787450505125883330921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20994099868013669022215789 7872787450505125883330921)
  ·
    refine ⟨5904590587878844412498191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7872787450505125883330921 5904590587878844412498191)
    ·
      refine ⟨8856885881818266618747287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5904590587878844412498191 8856885881818266618747287)
      ·
        refine ⟨13285328822727399928120931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8856885881818266618747287 13285328822727399928120931)
        ·
          refine ⟨19927993234091099892181397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13285328822727399928120931 19927993234091099892181397)
          ·
            refine ⟨934124682848020307446003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 19927993234091099892181397 934124682848020307446003)
            ·
              refine ⟨1401187024272030461169005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 934124682848020307446003 1401187024272030461169005)
              ·
                refine ⟨525445134102011422938377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1401187024272030461169005 525445134102011422938377)
                ·
                  refine ⟨394083850576508567203783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 525445134102011422938377 394083850576508567203783)
                  ·
                    rfl

theorem cell20_863410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 1, 3, 2].length) (baseStart_863410 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_863410 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_863410 prefixEnd_863410 := by exact prefixLift 863410
  have htrace : WordTrace (prefixWord ++ tailWord_863410) baseStart_863410 baseEnd_863410 := by
    simpa [prefixWord, tailWord_863410, baseEnd_863410] using wordTrace_append hprefix tailTrace_863410
  have hstable : (prefixWord ++ tailWord_863410).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_863410).length < 2 ^ (prefixWord ++ tailWord_863410).sum := by decide
  have hdescent : baseEnd_863410 < baseStart_863410 := by decide
  rcases family_descends (prefixWord ++ tailWord_863410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_863435 : List Nat := [1, 1, 1, 1, 3, 2, 2, 5, 4]
def baseStart_863435 : Nat := 118140960795 + 863435 * 2 ^ 59
def prefixEnd_863435 : Nat := 4983230072969 + 3 ^ 40 * 863435 * 2
def baseEnd_863435 : Nat := 394095261257719591370347

theorem tailTrace_863435 : CollatzResearch.WordTrace tailWord_863435 prefixEnd_863435 394095261257719591370347 := by
  unfold tailWord_863435
  simp only [CollatzResearch.WordTrace]
  refine ⟨31492061626929932802983759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20994707751286621868655839 31492061626929932802983759)
  ·
    refine ⟨47238092440394899204475639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31492061626929932802983759 47238092440394899204475639)
    ·
      refine ⟨70857138660592348806713459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47238092440394899204475639 70857138660592348806713459)
      ·
        refine ⟨106285707990888523210070189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70857138660592348806713459 106285707990888523210070189)
        ·
          refine ⟨39857140496583196203776321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106285707990888523210070189 39857140496583196203776321)
          ·
            refine ⟨29892855372437397152832241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39857140496583196203776321 29892855372437397152832241)
            ·
              refine ⟨22419641529328047864624181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29892855372437397152832241 22419641529328047864624181)
              ·
                refine ⟨2101841393374504487308517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22419641529328047864624181 2101841393374504487308517)
                ·
                  refine ⟨394095261257719591370347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2101841393374504487308517 394095261257719591370347)
                  ·
                    rfl

theorem cell20_863435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 5, 4].length) (baseStart_863435 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_863435 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_863435 prefixEnd_863435 := by exact prefixLift 863435
  have htrace : WordTrace (prefixWord ++ tailWord_863435) baseStart_863435 baseEnd_863435 := by
    simpa [prefixWord, tailWord_863435, baseEnd_863435] using wordTrace_append hprefix tailTrace_863435
  have hstable : (prefixWord ++ tailWord_863435).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_863435).length < 2 ^ (prefixWord ++ tailWord_863435).sum := by decide
  have hdescent : baseEnd_863435 < baseStart_863435 := by decide
  rcases family_descends (prefixWord ++ tailWord_863435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_863437 : List Nat := [1, 6, 2, 2, 1, 2, 2, 1, 3]
def baseStart_863437 : Nat := 118140960795 + 863437 * 2 ^ 59
def prefixEnd_863437 : Nat := 4983230072969 + 3 ^ 40 * 863437 * 2
def baseEnd_863437 : Nat := 394096174112216473303673

theorem tailTrace_863437 : CollatzResearch.WordTrace tailWord_863437 prefixEnd_863437 394096174112216473303673 := by
  unfold tailWord_863437
  simp only [CollatzResearch.WordTrace]
  refine ⟨31492134572922687144556565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20994756381948458096371043 31492134572922687144556565)
  ·
    refine ⟨1476193808105750959901089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 31492134572922687144556565 1476193808105750959901089)
    ·
      refine ⟨1107145356079313219925817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1476193808105750959901089 1107145356079313219925817)
      ·
        refine ⟨830359017059484914944363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1107145356079313219925817 830359017059484914944363)
        ·
          refine ⟨1245538525589227372416545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 830359017059484914944363 1245538525589227372416545)
          ·
            refine ⟨934153894191920529312409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1245538525589227372416545 934153894191920529312409)
            ·
              refine ⟨700615420643940396984307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 934153894191920529312409 700615420643940396984307)
              ·
                refine ⟨1050923130965910595476461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 700615420643940396984307 1050923130965910595476461)
                ·
                  refine ⟨394096174112216473303673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1050923130965910595476461 394096174112216473303673)
                  ·
                    rfl

theorem cell20_863437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 2, 1, 3].length) (baseStart_863437 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_863437 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_863437 prefixEnd_863437 := by exact prefixLift 863437
  have htrace : WordTrace (prefixWord ++ tailWord_863437) baseStart_863437 baseEnd_863437 := by
    simpa [prefixWord, tailWord_863437, baseEnd_863437] using wordTrace_append hprefix tailTrace_863437
  have hstable : (prefixWord ++ tailWord_863437).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_863437).length < 2 ^ (prefixWord ++ tailWord_863437).sum := by decide
  have hdescent : baseEnd_863437 < baseStart_863437 := by decide
  rcases family_descends (prefixWord ++ tailWord_863437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_863438 : List Nat := [4, 1, 1, 1, 5, 1, 2, 5]
def baseStart_863438 : Nat := 118140960795 + 863438 * 2 ^ 59
def prefixEnd_863438 : Nat := 4983230072969 + 3 ^ 40 * 863438 * 2
def baseEnd_863438 : Nat := 131365543513154971423445

theorem tailTrace_863438 : CollatzResearch.WordTrace tailWord_863438 prefixEnd_863438 131365543513154971423445 := by
  unfold tailWord_863438
  simp only [CollatzResearch.WordTrace]
  refine ⟨3936521380739883039417871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20994780697279376210228645 3936521380739883039417871)
  ·
    refine ⟨5904782071109824559126807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3936521380739883039417871 5904782071109824559126807)
    ·
      refine ⟨8857173106664736838690211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5904782071109824559126807 8857173106664736838690211)
      ·
        refine ⟨13285759659997105258035317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8857173106664736838690211 13285759659997105258035317)
        ·
          refine ⟨1245539968124728617940811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13285759659997105258035317 1245539968124728617940811)
          ·
            refine ⟨1868309952187092926911217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1245539968124728617940811 1868309952187092926911217)
            ·
              refine ⟨1401232464140319695183413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1868309952187092926911217 1401232464140319695183413)
              ·
                refine ⟨131365543513154971423445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1401232464140319695183413 131365543513154971423445)
                ·
                  rfl

theorem cell20_863438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 2, 5].length) (baseStart_863438 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_863438 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_863438 prefixEnd_863438 := by exact prefixLift 863438
  have htrace : WordTrace (prefixWord ++ tailWord_863438) baseStart_863438 baseEnd_863438 := by
    simpa [prefixWord, tailWord_863438, baseEnd_863438] using wordTrace_append hprefix tailTrace_863438
  have hstable : (prefixWord ++ tailWord_863438).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_863438).length < 2 ^ (prefixWord ++ tailWord_863438).sum := by decide
  have hdescent : baseEnd_863438 < baseStart_863438 := by decide
  rcases family_descends (prefixWord ++ tailWord_863438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_863486 : List Nat := [4, 2, 2, 1, 1, 3, 1, 4, 2]
def baseStart_863486 : Nat := 118140960795 + 863486 * 2 ^ 59
def prefixEnd_863486 : Nat := 4983230072969 + 3 ^ 40 * 863486 * 2
def baseEnd_863486 : Nat := 394118539047390080670139

theorem tailTrace_863486 : CollatzResearch.WordTrace tailWord_863486 prefixEnd_863486 394118539047390080670139 := by
  unfold tailWord_863486
  simp only [CollatzResearch.WordTrace]
  refine ⟨3936740218718146064136289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20995947833163445675393541 3936740218718146064136289)
  ·
    refine ⟨2952555164038609548102217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3936740218718146064136289 2952555164038609548102217)
    ·
      refine ⟨2214416373028957161076663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2952555164038609548102217 2214416373028957161076663)
      ·
        refine ⟨3321624559543435741614995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2214416373028957161076663 3321624559543435741614995)
        ·
          refine ⟨4982436839315153612422493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3321624559543435741614995 4982436839315153612422493)
          ·
            refine ⟨1868413814743182604658435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4982436839315153612422493 1868413814743182604658435)
            ·
              refine ⟨2802620722114773906987653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1868413814743182604658435 2802620722114773906987653)
              ·
                refine ⟨525491385396520107560185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2802620722114773906987653 525491385396520107560185)
                ·
                  refine ⟨394118539047390080670139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 525491385396520107560185 394118539047390080670139)
                  ·
                    rfl

theorem cell20_863486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 1, 4, 2].length) (baseStart_863486 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_863486 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_863486 prefixEnd_863486 := by exact prefixLift 863486
  have htrace : WordTrace (prefixWord ++ tailWord_863486) baseStart_863486 baseEnd_863486 := by
    simpa [prefixWord, tailWord_863486, baseEnd_863486] using wordTrace_append hprefix tailTrace_863486
  have hstable : (prefixWord ++ tailWord_863486).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_863486).length < 2 ^ (prefixWord ++ tailWord_863486).sum := by decide
  have hdescent : baseEnd_863486 < baseStart_863486 := by decide
  rcases family_descends (prefixWord ++ tailWord_863486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_863514 : List Nat := [3, 1, 1, 3, 3, 2, 3, 4]
def baseStart_863514 : Nat := 118140960795 + 863514 * 2 ^ 59
def prefixEnd_863514 : Nat := 4983230072969 + 3 ^ 40 * 863514 * 2
def baseEnd_863514 : Nat := 131377106336782142578897

theorem tailTrace_863514 : CollatzResearch.WordTrace tailWord_863514 prefixEnd_863514 131377106336782142578897 := by
  unfold tailWord_863514
  simp only [CollatzResearch.WordTrace]
  refine ⟨7873735748410932323777399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20996628662429152863406397 7873735748410932323777399)
  ·
    refine ⟨11810603622616398485666099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7873735748410932323777399 11810603622616398485666099)
    ·
      refine ⟨17715905433924597728499149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11810603622616398485666099 17715905433924597728499149)
      ·
        refine ⟨6643464537721724148187181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17715905433924597728499149 6643464537721724148187181)
        ·
          refine ⟨2491299201645646555570193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6643464537721724148187181 2491299201645646555570193)
          ·
            refine ⟨1868474401234234916677645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2491299201645646555570193 1868474401234234916677645)
            ·
              refine ⟨700677900462838093754117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1868474401234234916677645 700677900462838093754117)
              ·
                refine ⟨131377106336782142578897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 700677900462838093754117 131377106336782142578897)
                ·
                  rfl

theorem cell20_863514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 3, 4].length) (baseStart_863514 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_863514 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_863514 prefixEnd_863514 := by exact prefixLift 863514
  have htrace : WordTrace (prefixWord ++ tailWord_863514) baseStart_863514 baseEnd_863514 := by
    simpa [prefixWord, tailWord_863514, baseEnd_863514] using wordTrace_append hprefix tailTrace_863514
  have hstable : (prefixWord ++ tailWord_863514).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_863514).length < 2 ^ (prefixWord ++ tailWord_863514).sum := by decide
  have hdescent : baseEnd_863514 < baseStart_863514 := by decide
  rcases family_descends (prefixWord ++ tailWord_863514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_863538 : List Nat := [3, 2, 1, 1, 4, 3, 1, 2, 3]
def baseStart_863538 : Nat := 118140960795 + 863538 * 2 ^ 59
def prefixEnd_863538 : Nat := 4983230072969 + 3 ^ 40 * 863538 * 2
def baseEnd_863538 : Nat := 394142273264309010936593

theorem tailTrace_863538 : CollatzResearch.WordTrace tailWord_863538 prefixEnd_863538 394142273264309010936593 := by
  unfold tailWord_863538
  simp only [CollatzResearch.WordTrace]
  refine ⟨7873954586389195348495817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20997212230371187595988845 7873954586389195348495817)
  ·
    refine ⟨5905465939791896511371863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7873954586389195348495817 5905465939791896511371863)
    ·
      refine ⟨8858198909687844767057795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5905465939791896511371863 8858198909687844767057795)
      ·
        refine ⟨13287298364531767150586693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8858198909687844767057795 13287298364531767150586693)
        ·
          refine ⟨2491368443349706340735005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13287298364531767150586693 2491368443349706340735005)
          ·
            refine ⟨934263166256139877775627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2491368443349706340735005 934263166256139877775627)
            ·
              refine ⟨1401394749384209816663441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 934263166256139877775627 1401394749384209816663441)
              ·
                refine ⟨1051046062038157362497581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1401394749384209816663441 1051046062038157362497581)
                ·
                  refine ⟨394142273264309010936593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1051046062038157362497581 394142273264309010936593)
                  ·
                    rfl

theorem cell20_863538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 1, 2, 3].length) (baseStart_863538 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_863538 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_863538 prefixEnd_863538 := by exact prefixLift 863538
  have htrace : WordTrace (prefixWord ++ tailWord_863538) baseStart_863538 baseEnd_863538 := by
    simpa [prefixWord, tailWord_863538, baseEnd_863538] using wordTrace_append hprefix tailTrace_863538
  have hstable : (prefixWord ++ tailWord_863538).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_863538).length < 2 ^ (prefixWord ++ tailWord_863538).sum := by decide
  have hdescent : baseEnd_863538 < baseStart_863538 := by decide
  rcases family_descends (prefixWord ++ tailWord_863538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_863545 : List Nat := [1, 2, 1, 6, 2, 1, 2, 1, 4]
def baseStart_863545 : Nat := 118140960795 + 863545 * 2 ^ 59
def prefixEnd_863545 : Nat := 4983230072969 + 3 ^ 40 * 863545 * 2
def baseEnd_863545 : Nat := 394145468255048097703231

theorem tailTrace_863545 : CollatzResearch.WordTrace tailWord_863545 prefixEnd_863545 394145468255048097703231 := by
  unfold tailWord_863545
  simp only [CollatzResearch.WordTrace]
  refine ⟨31496073656531421589488089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20997382437687614392992059 31496073656531421589488089)
  ·
    refine ⟨23622055242398566192116067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31496073656531421589488089 23622055242398566192116067)
    ·
      refine ⟨35433082863597849288174101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23622055242398566192116067 35433082863597849288174101)
      ·
        refine ⟨1660925759231149185383161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 35433082863597849288174101 1660925759231149185383161)
        ·
          refine ⟨1245694319423361889037371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1660925759231149185383161 1245694319423361889037371)
          ·
            refine ⟨1868541479135042833556057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1245694319423361889037371 1868541479135042833556057)
            ·
              refine ⟨1401406109351282125167043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1868541479135042833556057 1401406109351282125167043)
              ·
                refine ⟨2102109164026923187750565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1401406109351282125167043 2102109164026923187750565)
                ·
                  refine ⟨394145468255048097703231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2102109164026923187750565 394145468255048097703231)
                  ·
                    rfl

theorem cell20_863545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 2, 1, 4].length) (baseStart_863545 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_863545 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_863545 prefixEnd_863545 := by exact prefixLift 863545
  have htrace : WordTrace (prefixWord ++ tailWord_863545) baseStart_863545 baseEnd_863545 := by
    simpa [prefixWord, tailWord_863545, baseEnd_863545] using wordTrace_append hprefix tailTrace_863545
  have hstable : (prefixWord ++ tailWord_863545).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_863545).length < 2 ^ (prefixWord ++ tailWord_863545).sum := by decide
  have hdescent : baseEnd_863545 < baseStart_863545 := by decide
  rcases family_descends (prefixWord ++ tailWord_863545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
