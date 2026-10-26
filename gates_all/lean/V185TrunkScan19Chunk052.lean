import V185TrunkScan19Chunk051

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental

namespace V185TrunkScan19Incremental

def tailWord_521455 : List Nat := [1, 1, 2, 1, 8, 1, 1, 4]
def baseStart_521455 : Nat := 118140960795 + 521455 * 2 ^ 59
def prefixEnd_521455 : Nat := 4983230072969 + 3 ^ 40 * 521455 * 2
def baseEnd_521455 : Nat := 158670847223918541401113

theorem tailTrace_521455 : CollatzResearch.WordTrace tailWord_521455 prefixEnd_521455 158670847223918541401113 := by
  unfold tailWord_521455
  simp only [CollatzResearch.WordTrace]
  refine ⟨19019026325865067268885819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12679350883910044845923879 19019026325865067268885819)
  ·
    refine ⟨28528539488797600903328729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19019026325865067268885819 28528539488797600903328729)
    ·
      refine ⟨21396404616598200677496547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28528539488797600903328729 21396404616598200677496547)
      ·
        refine ⟨32094606924897301016244821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21396404616598200677496547 32094606924897301016244821)
        ·
          refine ⟨376108674901140246284119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 32094606924897301016244821 376108674901140246284119)
          ·
            refine ⟨564163012351710369426179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 376108674901140246284119 564163012351710369426179)
            ·
              refine ⟨846244518527565554139269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 564163012351710369426179 846244518527565554139269)
              ·
                refine ⟨158670847223918541401113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 846244518527565554139269 158670847223918541401113)
                ·
                  rfl

theorem cell19_521455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 1, 4].length) (baseStart_521455 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_521455 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_521455 prefixEnd_521455 := by exact prefixLift 521455
  have htrace : WordTrace (prefixWord ++ tailWord_521455) baseStart_521455 baseEnd_521455 := by
    simpa [prefixWord, tailWord_521455, baseEnd_521455] using wordTrace_append hprefix tailTrace_521455
  have hstable : (prefixWord ++ tailWord_521455).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521455).length < 2 ^ (prefixWord ++ tailWord_521455).sum := by decide
  have hdescent : baseEnd_521455 < baseStart_521455 := by decide
  rcases family_descends (prefixWord ++ tailWord_521455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521459 : List Nat := [1, 1, 1, 2, 2, 5, 3, 4]
def baseStart_521459 : Nat := 118140960795 + 521459 * 2 ^ 59
def prefixEnd_521459 : Nat := 4983230072969 + 3 ^ 40 * 521459 * 2
def baseEnd_521459 : Nat := 158672064363247717312213

theorem tailTrace_521459 : CollatzResearch.WordTrace tailWord_521459 prefixEnd_521459 158672064363247717312213 := by
  unfold tailWord_521459
  simp only [CollatzResearch.WordTrace]
  refine ⟨19019172217850575952031431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12679448145233717301354287 19019172217850575952031431)
  ·
    refine ⟨28528758326775863928047147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19019172217850575952031431 28528758326775863928047147)
    ·
      refine ⟨42793137490163795892070721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28528758326775863928047147 42793137490163795892070721)
      ·
        refine ⟨32094853117622846919053041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42793137490163795892070721 32094853117622846919053041)
        ·
          refine ⟨24071139838217135189289781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32094853117622846919053041 24071139838217135189289781)
          ·
            refine ⟨2256669359832856423995917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 24071139838217135189289781 2256669359832856423995917)
            ·
              refine ⟨846251009937321158998469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2256669359832856423995917 846251009937321158998469)
              ·
                refine ⟨158672064363247717312213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 846251009937321158998469 158672064363247717312213)
                ·
                  rfl

theorem cell19_521459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 3, 4].length) (baseStart_521459 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_521459 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_521459 prefixEnd_521459 := by exact prefixLift 521459
  have htrace : WordTrace (prefixWord ++ tailWord_521459) baseStart_521459 baseEnd_521459 := by
    simpa [prefixWord, tailWord_521459, baseEnd_521459] using wordTrace_append hprefix tailTrace_521459
  have hstable : (prefixWord ++ tailWord_521459).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521459).length < 2 ^ (prefixWord ++ tailWord_521459).sum := by decide
  have hdescent : baseEnd_521459 < baseStart_521459 := by decide
  rcases family_descends (prefixWord ++ tailWord_521459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521529 : List Nat := [1, 2, 1, 6, 3, 1, 2, 3]
def baseStart_521529 : Nat := 118140960795 + 521529 * 2 ^ 59
def prefixEnd_521529 : Nat := 4983230072969 + 3 ^ 40 * 521529 * 2
def baseEnd_521529 : Nat := 158693364301508295756467

theorem tailTrace_521529 : CollatzResearch.WordTrace tailWord_521529 prefixEnd_521529 158693364301508295756467 := by
  unfold tailWord_521529
  simp only [CollatzResearch.WordTrace]
  refine ⟨19021725327596977907079641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12681150218397985271386427 19021725327596977907079641)
  ·
    refine ⟨14266293995697733430309731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19021725327596977907079641 14266293995697733430309731)
    ·
      refine ⟨21399440993546600145464597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14266293995697733430309731 21399440993546600145464597)
      ·
        refine ⟨1003098796572496881818653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 21399440993546600145464597 1003098796572496881818653)
        ·
          refine ⟨376162048714686330681995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1003098796572496881818653 376162048714686330681995)
          ·
            refine ⟨564243073072029496022993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 376162048714686330681995 564243073072029496022993)
            ·
              refine ⟨423182304804022122017245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 564243073072029496022993 423182304804022122017245)
              ·
                refine ⟨158693364301508295756467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 423182304804022122017245 158693364301508295756467)
                ·
                  rfl

theorem cell19_521529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 2, 3].length) (baseStart_521529 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_521529 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_521529 prefixEnd_521529 := by exact prefixLift 521529
  have htrace : WordTrace (prefixWord ++ tailWord_521529) baseStart_521529 baseEnd_521529 := by
    simpa [prefixWord, tailWord_521529, baseEnd_521529] using wordTrace_append hprefix tailTrace_521529
  have hstable : (prefixWord ++ tailWord_521529).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521529).length < 2 ^ (prefixWord ++ tailWord_521529).sum := by decide
  have hdescent : baseEnd_521529 < baseStart_521529 := by decide
  rcases family_descends (prefixWord ++ tailWord_521529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521535 : List Nat := [1, 1, 2, 2, 4, 3, 1, 5]
def baseStart_521535 : Nat := 118140960795 + 521535 * 2 ^ 59
def prefixEnd_521535 : Nat := 4983230072969 + 3 ^ 40 * 521535 * 2
def baseEnd_521535 : Nat := 158695190010502059623117

theorem tailTrace_521535 : CollatzResearch.WordTrace tailWord_521535 prefixEnd_521535 158695190010502059623117 := by
  unfold tailWord_521535
  simp only [CollatzResearch.WordTrace]
  refine ⟨19021944165575240931798059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12681296110383493954532039 19021944165575240931798059)
  ·
    refine ⟨28532916248362861397697089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19021944165575240931798059 28532916248362861397697089)
    ·
      refine ⟨21399687186272146048272817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28532916248362861397697089 21399687186272146048272817)
      ·
        refine ⟨16049765389704109536204613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21399687186272146048272817 16049765389704109536204613)
        ·
          refine ⟨3009331010569520538038365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16049765389704109536204613 3009331010569520538038365)
          ·
            refine ⟨1128499128963570201764387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3009331010569520538038365 1128499128963570201764387)
            ·
              refine ⟨1692748693445355302646581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1128499128963570201764387 1692748693445355302646581)
              ·
                refine ⟨158695190010502059623117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1692748693445355302646581 158695190010502059623117)
                ·
                  rfl

theorem cell19_521535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 1, 5].length) (baseStart_521535 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_521535 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_521535 prefixEnd_521535 := by exact prefixLift 521535
  have htrace : WordTrace (prefixWord ++ tailWord_521535) baseStart_521535 baseEnd_521535 := by
    simpa [prefixWord, tailWord_521535, baseEnd_521535] using wordTrace_append hprefix tailTrace_521535
  have hstable : (prefixWord ++ tailWord_521535).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521535).length < 2 ^ (prefixWord ++ tailWord_521535).sum := by decide
  have hdescent : baseEnd_521535 < baseStart_521535 := by decide
  rcases family_descends (prefixWord ++ tailWord_521535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521573 : List Nat := [1, 3, 1, 3, 1, 2, 4, 4]
def baseStart_521573 : Nat := 118140960795 + 521573 * 2 ^ 59
def prefixEnd_521573 : Nat := 4983230072969 + 3 ^ 40 * 521573 * 2
def baseEnd_521573 : Nat := 158706752834129230778569

theorem tailTrace_521573 : CollatzResearch.WordTrace tailWord_521573 prefixEnd_521573 158706752834129230778569 := by
  unfold tailWord_521573
  simp only [CollatzResearch.WordTrace]
  refine ⟨19023330139437573421681373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12682220092958382281120915 19023330139437573421681373)
  ·
    refine ⟨7133748802289090033130515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19023330139437573421681373 7133748802289090033130515)
    ·
      refine ⟨10700623203433635049695773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7133748802289090033130515 10700623203433635049695773)
      ·
        refine ⟨4012733701287613143635915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10700623203433635049695773 4012733701287613143635915)
        ·
          refine ⟨6019100551931419715453873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4012733701287613143635915 6019100551931419715453873)
          ·
            refine ⟨4514325413948564786590405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6019100551931419715453873 4514325413948564786590405)
            ·
              refine ⟨846436015115355897485701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4514325413948564786590405 846436015115355897485701)
              ·
                refine ⟨158706752834129230778569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 846436015115355897485701 158706752834129230778569)
                ·
                  rfl

theorem cell19_521573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 4, 4].length) (baseStart_521573 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_521573 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_521573 prefixEnd_521573 := by exact prefixLift 521573
  have htrace : WordTrace (prefixWord ++ tailWord_521573) baseStart_521573 baseEnd_521573 := by
    simpa [prefixWord, tailWord_521573, baseEnd_521573] using wordTrace_append hprefix tailTrace_521573
  have hstable : (prefixWord ++ tailWord_521573).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521573).length < 2 ^ (prefixWord ++ tailWord_521573).sum := by decide
  have hdescent : baseEnd_521573 < baseStart_521573 := by decide
  rcases family_descends (prefixWord ++ tailWord_521573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521645 : List Nat := [1, 5, 2, 2, 1, 2, 3, 3]
def baseStart_521645 : Nat := 118140960795 + 521645 * 2 ^ 59
def prefixEnd_521645 : Nat := 4983230072969 + 3 ^ 40 * 521645 * 2
def baseEnd_521645 : Nat := 158728661342054397178373

theorem tailTrace_521645 : CollatzResearch.WordTrace tailWord_521645 prefixEnd_521645 158728661342054397178373 := by
  unfold tailWord_521645
  simp only [CollatzResearch.WordTrace]
  refine ⟨19025956195176729718302389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12683970796784486478868259 19025956195176729718302389)
  ·
    refine ⟨1783683393297818411090849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 19025956195176729718302389 1783683393297818411090849)
    ·
      refine ⟨1337762544973363808318137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1783683393297818411090849 1337762544973363808318137)
      ·
        refine ⟨1003321908730022856238603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1337762544973363808318137 1003321908730022856238603)
        ·
          refine ⟨1504982863095034284357905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1003321908730022856238603 1504982863095034284357905)
          ·
            refine ⟨1128737147321275713268429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1504982863095034284357905 1128737147321275713268429)
            ·
              refine ⟨423276430245478392475661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1128737147321275713268429 423276430245478392475661)
              ·
                refine ⟨158728661342054397178373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 423276430245478392475661 158728661342054397178373)
                ·
                  rfl

theorem cell19_521645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 3, 3].length) (baseStart_521645 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_521645 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_521645 prefixEnd_521645 := by exact prefixLift 521645
  have htrace : WordTrace (prefixWord ++ tailWord_521645) baseStart_521645 baseEnd_521645 := by
    simpa [prefixWord, tailWord_521645, baseEnd_521645] using wordTrace_append hprefix tailTrace_521645
  have hstable : (prefixWord ++ tailWord_521645).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521645).length < 2 ^ (prefixWord ++ tailWord_521645).sum := by decide
  have hdescent : baseEnd_521645 < baseStart_521645 := by decide
  rcases family_descends (prefixWord ++ tailWord_521645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521651 : List Nat := [1, 1, 1, 2, 3, 1, 1, 9]
def baseStart_521651 : Nat := 118140960795 + 521651 * 2 ^ 59
def prefixEnd_521651 : Nat := 4983230072969 + 3 ^ 40 * 521651 * 2
def baseEnd_521651 : Nat := 158730487051048161045023

theorem tailTrace_521651 : CollatzResearch.WordTrace tailWord_521651 prefixEnd_521651 158730487051048161045023 := by
  unfold tailWord_521651
  simp only [CollatzResearch.WordTrace]
  refine ⟨19026175033154992743020807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12684116688769995162013871 19026175033154992743020807)
  ·
    refine ⟨28539262549732489114531211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19026175033154992743020807 28539262549732489114531211)
    ·
      refine ⟨42808893824598733671796817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28539262549732489114531211 42808893824598733671796817)
      ·
        refine ⟨32106670368449050253847613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42808893824598733671796817 32106670368449050253847613)
        ·
          refine ⟨12040001388168393845192855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32106670368449050253847613 12040001388168393845192855)
          ·
            refine ⟨18060002082252590767789283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12040001388168393845192855 18060002082252590767789283)
            ·
              refine ⟨27090003123378886151683925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18060002082252590767789283 27090003123378886151683925)
              ·
                refine ⟨158730487051048161045023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 27090003123378886151683925 158730487051048161045023)
                ·
                  rfl

theorem cell19_521651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 9].length) (baseStart_521651 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_521651 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_521651 prefixEnd_521651 := by exact prefixLift 521651
  have htrace : WordTrace (prefixWord ++ tailWord_521651) baseStart_521651 baseEnd_521651 := by
    simpa [prefixWord, tailWord_521651, baseEnd_521651] using wordTrace_append hprefix tailTrace_521651
  have hstable : (prefixWord ++ tailWord_521651).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521651).length < 2 ^ (prefixWord ++ tailWord_521651).sum := by decide
  have hdescent : baseEnd_521651 < baseStart_521651 := by decide
  rcases family_descends (prefixWord ++ tailWord_521651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521725 : List Nat := [1, 4, 1, 1, 1, 6, 5]
def baseStart_521725 : Nat := 118140960795 + 521725 * 2 ^ 59
def prefixEnd_521725 : Nat := 4983230072969 + 3 ^ 40 * 521725 * 2
def baseEnd_521725 : Nat := 52917668042879305133459

theorem tailTrace_521725 : CollatzResearch.WordTrace tailWord_521725 prefixEnd_521725 52917668042879305133459 := by
  unfold tailWord_521725
  simp only [CollatzResearch.WordTrace]
  refine ⟨19028874034886903381214629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12685916023257935587476419 19028874034886903381214629)
  ·
    refine ⟨3567913881541294383977743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19028874034886903381214629 3567913881541294383977743)
    ·
      refine ⟨5351870822311941575966615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3567913881541294383977743 5351870822311941575966615)
      ·
        refine ⟨8027806233467912363949923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5351870822311941575966615 8027806233467912363949923)
        ·
          refine ⟨12041709350201868545924885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8027806233467912363949923 12041709350201868545924885)
          ·
            refine ⟨564455125790712588090229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 12041709350201868545924885 564455125790712588090229)
            ·
              refine ⟨52917668042879305133459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 564455125790712588090229 52917668042879305133459)
              ·
                rfl

theorem cell19_521725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 5].length) (baseStart_521725 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_521725 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_521725 prefixEnd_521725 := by exact prefixLift 521725
  have htrace : WordTrace (prefixWord ++ tailWord_521725) baseStart_521725 baseEnd_521725 := by
    simpa [prefixWord, tailWord_521725, baseEnd_521725] using wordTrace_append hprefix tailTrace_521725
  have hstable : (prefixWord ++ tailWord_521725).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521725).length < 2 ^ (prefixWord ++ tailWord_521725).sum := by decide
  have hdescent : baseEnd_521725 < baseStart_521725 := by decide
  rcases family_descends (prefixWord ++ tailWord_521725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521742 : List Nat := [4, 1, 1, 2, 4, 1, 2, 4]
def baseStart_521742 : Nat := 118140960795 + 521742 * 2 ^ 59
def prefixEnd_521742 : Nat := 4983230072969 + 3 ^ 40 * 521742 * 2
def baseEnd_521742 : Nat := 158758176970786913022553

theorem tailTrace_521742 : CollatzResearch.WordTrace tailWord_521742 prefixEnd_521742 158758176970786913022553 := by
  unfold tailWord_521742
  simp only [CollatzResearch.WordTrace]
  refine ⟨2378686759478164410572935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12686329383883543523055653 2378686759478164410572935)
  ·
    refine ⟨3568030139217246615859403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2378686759478164410572935 3568030139217246615859403)
    ·
      refine ⟨5352045208825869923789105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3568030139217246615859403 5352045208825869923789105)
      ·
        refine ⟨4014033906619402442841829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5352045208825869923789105 4014033906619402442841829)
        ·
          refine ⟨752631357491137958032843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4014033906619402442841829 752631357491137958032843)
          ·
            refine ⟨1128947036236706937049265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 752631357491137958032843 1128947036236706937049265)
            ·
              refine ⟨846710277177530202786949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1128947036236706937049265 846710277177530202786949)
              ·
                refine ⟨158758176970786913022553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 846710277177530202786949 158758176970786913022553)
                ·
                  rfl

theorem cell19_521742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 2, 4].length) (baseStart_521742 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_521742 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_521742 prefixEnd_521742 := by exact prefixLift 521742
  have htrace : WordTrace (prefixWord ++ tailWord_521742) baseStart_521742 baseEnd_521742 := by
    simpa [prefixWord, tailWord_521742, baseEnd_521742] using wordTrace_append hprefix tailTrace_521742
  have hstable : (prefixWord ++ tailWord_521742).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521742).length < 2 ^ (prefixWord ++ tailWord_521742).sum := by decide
  have hdescent : baseEnd_521742 < baseStart_521742 := by decide
  rcases family_descends (prefixWord ++ tailWord_521742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521782 : List Nat := [5, 1, 2, 1, 10]
def baseStart_521782 : Nat := 118140960795 + 521782 * 2 ^ 59
def prefixEnd_521782 : Nat := 4983230072969 + 3 ^ 40 * 521782 * 2
def baseEnd_521782 : Nat := 5880383272743654523465

theorem tailTrace_521782 : CollatzResearch.WordTrace tailWord_521782 prefixEnd_521782 5880383272743654523465 := by
  unfold tailWord_521782
  simp only [CollatzResearch.WordTrace]
  refine ⟨1189434562230025132252475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12687301997120268077359733 1189434562230025132252475)
  ·
    refine ⟨1784151843345037698378713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1189434562230025132252475 1784151843345037698378713)
    ·
      refine ⟨1338113882508778273784035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1784151843345037698378713 1338113882508778273784035)
      ·
        refine ⟨2007170823763167410676053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1338113882508778273784035 2007170823763167410676053)
        ·
          refine ⟨5880383272743654523465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 2007170823763167410676053 5880383272743654523465)
          ·
            rfl

theorem cell19_521782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 10].length) (baseStart_521782 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_521782 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_521782 prefixEnd_521782 := by exact prefixLift 521782
  have htrace : WordTrace (prefixWord ++ tailWord_521782) baseStart_521782 baseEnd_521782 := by
    simpa [prefixWord, tailWord_521782, baseEnd_521782] using wordTrace_append hprefix tailTrace_521782
  have hstable : (prefixWord ++ tailWord_521782).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521782).length < 2 ^ (prefixWord ++ tailWord_521782).sum := by decide
  have hdescent : baseEnd_521782 < baseStart_521782 := by decide
  rcases family_descends (prefixWord ++ tailWord_521782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521784 : List Nat := [2, 1, 2, 1, 4, 9]
def baseStart_521784 : Nat := 118140960795 + 521784 * 2 ^ 59
def prefixEnd_521784 : Nat := 4983230072969 + 3 ^ 40 * 521784 * 2
def baseEnd_521784 : Nat := 17641217437082584454345

theorem tailTrace_521784 : CollatzResearch.WordTrace tailWord_521784 prefixEnd_521784 17641217437082584454345 := by
  unfold tailWord_521784
  simp only [CollatzResearch.WordTrace]
  refine ⟨9515512970836578228806203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12687350627782104305074937 9515512970836578228806203)
  ·
    refine ⟨14273269456254867343209305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9515512970836578228806203 14273269456254867343209305)
    ·
      refine ⟨10704952092191150507406979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14273269456254867343209305 10704952092191150507406979)
      ·
        refine ⟨16057428138286725761110469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10704952092191150507406979 16057428138286725761110469)
        ·
          refine ⟨3010767775928761080208213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16057428138286725761110469 3010767775928761080208213)
          ·
            refine ⟨17641217437082584454345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 3010767775928761080208213 17641217437082584454345)
            ·
              rfl

theorem cell19_521784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 9].length) (baseStart_521784 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_521784 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_521784 prefixEnd_521784 := by exact prefixLift 521784
  have htrace : WordTrace (prefixWord ++ tailWord_521784) baseStart_521784 baseEnd_521784 := by
    simpa [prefixWord, tailWord_521784, baseEnd_521784] using wordTrace_append hprefix tailTrace_521784
  have hstable : (prefixWord ++ tailWord_521784).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521784).length < 2 ^ (prefixWord ++ tailWord_521784).sum := by decide
  have hdescent : baseEnd_521784 < baseStart_521784 := by decide
  rcases family_descends (prefixWord ++ tailWord_521784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521799 : List Nat := [1, 1, 4, 1, 5, 2, 1, 4]
def baseStart_521799 : Nat := 118140960795 + 521799 * 2 ^ 59
def prefixEnd_521799 : Nat := 4983230072969 + 3 ^ 40 * 521799 * 2
def baseEnd_521799 : Nat := 158775521206227669755731

theorem tailTrace_521799 : CollatzResearch.WordTrace tailWord_521799 prefixEnd_521799 158775521206227669755731 := by
  unfold tailWord_521799
  simp only [CollatzResearch.WordTrace]
  refine ⟨19031573036618814019408451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12687715357745876012938967 19031573036618814019408451)
  ·
    refine ⟨28547359554928221029112677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19031573036618814019408451 28547359554928221029112677)
    ·
      refine ⟨5352629916549041442958627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28547359554928221029112677 5352629916549041442958627)
      ·
        refine ⟨8028944874823562164437941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5352629916549041442958627 8028944874823562164437941)
        ·
          refine ⟨752713582014708952916057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8028944874823562164437941 752713582014708952916057)
          ·
            refine ⟨564535186511031714687043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 752713582014708952916057 564535186511031714687043)
            ·
              refine ⟨846802779766547572030565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 564535186511031714687043 846802779766547572030565)
              ·
                refine ⟨158775521206227669755731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 846802779766547572030565 158775521206227669755731)
                ·
                  rfl

theorem cell19_521799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 1, 4].length) (baseStart_521799 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_521799 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_521799 prefixEnd_521799 := by exact prefixLift 521799
  have htrace : WordTrace (prefixWord ++ tailWord_521799) baseStart_521799 baseEnd_521799 := by
    simpa [prefixWord, tailWord_521799, baseEnd_521799] using wordTrace_append hprefix tailTrace_521799
  have hstable : (prefixWord ++ tailWord_521799).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521799).length < 2 ^ (prefixWord ++ tailWord_521799).sum := by decide
  have hdescent : baseEnd_521799 < baseStart_521799 := by decide
  rcases family_descends (prefixWord ++ tailWord_521799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521953 : List Nat := [1, 2, 3, 1, 6, 6]
def baseStart_521953 : Nat := 118140960795 + 521953 * 2 ^ 59
def prefixEnd_521953 : Nat := 4983230072969 + 3 ^ 40 * 521953 * 2
def baseEnd_521953 : Nat := 17646931230044549148121

theorem tailTrace_521953 : CollatzResearch.WordTrace tailWord_521953 prefixEnd_521953 17646931230044549148121 := by
  unfold tailWord_521953
  simp only [CollatzResearch.WordTrace]
  refine ⟨19037189878060898320514513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12691459918707265547009675 19037189878060898320514513)
  ·
    refine ⟨14277892408545673740385885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19037189878060898320514513 14277892408545673740385885)
    ·
      refine ⟨5354209653204627652644707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14277892408545673740385885 5354209653204627652644707)
      ·
        refine ⟨8031314479806941478967061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5354209653204627652644707 8031314479806941478967061)
        ·
          refine ⟨376467866240950381826581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 8031314479806941478967061 376467866240950381826581)
          ·
            refine ⟨17646931230044549148121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 376467866240950381826581 17646931230044549148121)
            ·
              rfl

theorem cell19_521953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 6].length) (baseStart_521953 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_521953 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_521953 prefixEnd_521953 := by exact prefixLift 521953
  have htrace : WordTrace (prefixWord ++ tailWord_521953) baseStart_521953 baseEnd_521953 := by
    simpa [prefixWord, tailWord_521953, baseEnd_521953] using wordTrace_append hprefix tailTrace_521953
  have hstable : (prefixWord ++ tailWord_521953).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521953).length < 2 ^ (prefixWord ++ tailWord_521953).sum := by decide
  have hdescent : baseEnd_521953 < baseStart_521953 := by decide
  rcases family_descends (prefixWord ++ tailWord_521953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521955 : List Nat := [1, 1, 1, 7, 9]
def baseStart_521955 : Nat := 118140960795 + 521955 * 2 ^ 59
def prefixEnd_521955 : Nat := 4983230072969 + 3 ^ 40 * 521955 * 2
def baseEnd_521955 : Nat := 5882332949632056677357

theorem tailTrace_521955 : CollatzResearch.WordTrace tailWord_521955 prefixEnd_521955 5882332949632056677357 := by
  unfold tailWord_521955
  simp only [CollatzResearch.WordTrace]
  refine ⟨19037262824053652662087319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12691508549369101774724879 19037262824053652662087319)
  ·
    refine ⟨28555894236080478993130979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19037262824053652662087319 28555894236080478993130979)
    ·
      refine ⟨42833841354120718489696469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28555894236080478993130979 42833841354120718489696469)
      ·
        refine ⟨1003918156737204339602261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 42833841354120718489696469 1003918156737204339602261)
        ·
          refine ⟨5882332949632056677357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 1003918156737204339602261 5882332949632056677357)
          ·
            rfl

theorem cell19_521955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 9].length) (baseStart_521955 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_521955 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_521955 prefixEnd_521955 := by exact prefixLift 521955
  have htrace : WordTrace (prefixWord ++ tailWord_521955) baseStart_521955 baseEnd_521955 := by
    simpa [prefixWord, tailWord_521955, baseEnd_521955] using wordTrace_append hprefix tailTrace_521955
  have hstable : (prefixWord ++ tailWord_521955).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521955).length < 2 ^ (prefixWord ++ tailWord_521955).sum := by decide
  have hdescent : baseEnd_521955 < baseStart_521955 := by decide
  rcases family_descends (prefixWord ++ tailWord_521955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522012 : List Nat := [2, 2, 3, 1, 1, 2, 8]
def baseStart_522012 : Nat := 118140960795 + 522012 * 2 ^ 59
def prefixEnd_522012 : Nat := 4983230072969 + 3 ^ 40 * 522012 * 2
def baseEnd_522012 : Nat := 52946777958502095673939

theorem tailTrace_522012 : CollatzResearch.WordTrace tailWord_522012 prefixEnd_522012 52946777958502095673939 := by
  unfold tailWord_522012
  simp only [CollatzResearch.WordTrace]
  refine ⟨9519670892423575698456145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12692894523231434264608193 9519670892423575698456145)
  ·
    refine ⟨7139753169317681773842109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9519670892423575698456145 7139753169317681773842109)
    ·
      refine ⟨2677407438494130665190791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7139753169317681773842109 2677407438494130665190791)
      ·
        refine ⟨4016111157741195997786187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2677407438494130665190791 4016111157741195997786187)
        ·
          refine ⟨6024166736611793996679281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4016111157741195997786187 6024166736611793996679281)
          ·
            refine ⟨4518125052458845497509461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6024166736611793996679281 4518125052458845497509461)
            ·
              refine ⟨52946777958502095673939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4518125052458845497509461 52946777958502095673939)
              ·
                rfl

theorem cell19_522012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 8].length) (baseStart_522012 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_522012 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_522012 prefixEnd_522012 := by exact prefixLift 522012
  have htrace : WordTrace (prefixWord ++ tailWord_522012) baseStart_522012 baseEnd_522012 := by
    simpa [prefixWord, tailWord_522012, baseEnd_522012] using wordTrace_append hprefix tailTrace_522012
  have hstable : (prefixWord ++ tailWord_522012).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522012).length < 2 ^ (prefixWord ++ tailWord_522012).sum := by decide
  have hdescent : baseEnd_522012 < baseStart_522012 := by decide
  rcases family_descends (prefixWord ++ tailWord_522012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522046 : List Nat := [4, 2, 1, 2, 2, 1, 4, 3]
def baseStart_522046 : Nat := 118140960795 + 522046 * 2 ^ 59
def prefixEnd_522046 : Nat := 4983230072969 + 3 ^ 40 * 522046 * 2
def baseEnd_522046 : Nat := 158850679559804282266169

theorem tailTrace_522046 : CollatzResearch.WordTrace tailWord_522046 prefixEnd_522046 158850679559804282266169 := by
  unfold tailWord_522046
  simp only [CollatzResearch.WordTrace]
  refine ⟨2380072733340496900456249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12693721244482650135766661 2380072733340496900456249)
  ·
    refine ⟨1785054550005372675342187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2380072733340496900456249 1785054550005372675342187)
    ·
      refine ⟨2677581825008059013013281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1785054550005372675342187 2677581825008059013013281)
      ·
        refine ⟨2008186368756044259759961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2677581825008059013013281 2008186368756044259759961)
        ·
          refine ⟨1506139776567033194819971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2008186368756044259759961 1506139776567033194819971)
          ·
            refine ⟨2259209664850549792229957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1506139776567033194819971 2259209664850549792229957)
            ·
              refine ⟨423601812159478086043117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2259209664850549792229957 423601812159478086043117)
              ·
                refine ⟨158850679559804282266169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 423601812159478086043117 158850679559804282266169)
                ·
                  rfl

theorem cell19_522046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 4, 3].length) (baseStart_522046 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_522046 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_522046 prefixEnd_522046 := by exact prefixLift 522046
  have htrace : WordTrace (prefixWord ++ tailWord_522046) baseStart_522046 baseEnd_522046 := by
    simpa [prefixWord, tailWord_522046, baseEnd_522046] using wordTrace_append hprefix tailTrace_522046
  have hstable : (prefixWord ++ tailWord_522046).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522046).length < 2 ^ (prefixWord ++ tailWord_522046).sum := by decide
  have hdescent : baseEnd_522046 < baseStart_522046 := by decide
  rcases family_descends (prefixWord ++ tailWord_522046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522069 : List Nat := [1, 3, 2, 2, 2, 2, 7]
def baseStart_522069 : Nat := 118140960795 + 522069 * 2 ^ 59
def prefixEnd_522069 : Nat := 4983230072969 + 3 ^ 40 * 522069 * 2
def baseEnd_522069 : Nat := 52952559370315681251665

theorem tailTrace_522069 : CollatzResearch.WordTrace tailWord_522069 prefixEnd_522069 52952559370315681251665 := by
  unfold tailWord_522069
  simp only [CollatzResearch.WordTrace]
  refine ⟨19041420745640650131737261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12694280497093766754491507 19041420745640650131737261)
  ·
    refine ⟨7140532779615243799401473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19041420745640650131737261 7140532779615243799401473)
    ·
      refine ⟨5355399584711432849551105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7140532779615243799401473 5355399584711432849551105)
      ·
        refine ⟨4016549688533574637163329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5355399584711432849551105 4016549688533574637163329)
        ·
          refine ⟨3012412266400180977872497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4016549688533574637163329 3012412266400180977872497)
          ·
            refine ⟨2259309199800135733404373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3012412266400180977872497 2259309199800135733404373)
            ·
              refine ⟨52952559370315681251665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2259309199800135733404373 52952559370315681251665)
              ·
                rfl

theorem cell19_522069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 7].length) (baseStart_522069 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_522069 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_522069 prefixEnd_522069 := by exact prefixLift 522069
  have htrace : WordTrace (prefixWord ++ tailWord_522069) baseStart_522069 baseEnd_522069 := by
    simpa [prefixWord, tailWord_522069, baseEnd_522069] using wordTrace_append hprefix tailTrace_522069
  have hstable : (prefixWord ++ tailWord_522069).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522069).length < 2 ^ (prefixWord ++ tailWord_522069).sum := by decide
  have hdescent : baseEnd_522069 < baseStart_522069 := by decide
  rcases family_descends (prefixWord ++ tailWord_522069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522215 : List Nat := [1, 1, 5, 2, 4, 1, 2, 3]
def baseStart_522215 : Nat := 118140960795 + 522215 * 2 ^ 59
def prefixEnd_522215 : Nat := 4983230072969 + 3 ^ 40 * 522215 * 2
def baseEnd_522215 : Nat := 158902103696461964510153

theorem tailTrace_522215 : CollatzResearch.WordTrace tailWord_522215 prefixEnd_522215 158902103696461964510153 := by
  unfold tailWord_522215
  simp only [CollatzResearch.WordTrace]
  refine ⟨19046745803111717066552099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12697830535407811377701399 19046745803111717066552099)
  ·
    refine ⟨28570118704667575599828149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19046745803111717066552099 28570118704667575599828149)
    ·
      refine ⟨2678448628562585212483889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 28570118704667575599828149 2678448628562585212483889)
      ·
        refine ⟨2008836471421938909362917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2678448628562585212483889 2008836471421938909362917)
        ·
          refine ⟨376656838391613545505547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2008836471421938909362917 376656838391613545505547)
          ·
            refine ⟨564985257587420318258321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 376656838391613545505547 564985257587420318258321)
            ·
              refine ⟨423738943190565238693741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 564985257587420318258321 423738943190565238693741)
              ·
                refine ⟨158902103696461964510153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 423738943190565238693741 158902103696461964510153)
                ·
                  rfl

theorem cell19_522215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 2, 3].length) (baseStart_522215 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_522215 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_522215 prefixEnd_522215 := by exact prefixLift 522215
  have htrace : WordTrace (prefixWord ++ tailWord_522215) baseStart_522215 baseEnd_522215 := by
    simpa [prefixWord, tailWord_522215, baseEnd_522215] using wordTrace_append hprefix tailTrace_522215
  have hstable : (prefixWord ++ tailWord_522215).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522215).length < 2 ^ (prefixWord ++ tailWord_522215).sum := by decide
  have hdescent : baseEnd_522215 < baseStart_522215 := by decide
  rcases family_descends (prefixWord ++ tailWord_522215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522238 : List Nat := [4, 2, 2, 2, 1, 1, 7]
def baseStart_522238 : Nat := 118140960795 + 522238 * 2 ^ 59
def prefixEnd_522238 : Nat := 4983230072969 + 3 ^ 40 * 522238 * 2
def baseEnd_522238 : Nat := 52969700749201575332993

theorem tailTrace_522238 : CollatzResearch.WordTrace tailWord_522238 prefixEnd_522238 52969700749201575332993 := by
  unfold tailWord_522238
  simp only [CollatzResearch.WordTrace]
  refine ⟨2380948085253548999329921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12698389788018927996426245 2380948085253548999329921)
  ·
    refine ⟨1785711063940161749497441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2380948085253548999329921 1785711063940161749497441)
    ·
      refine ⟨1339283297955121312123081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1785711063940161749497441 1339283297955121312123081)
      ·
        refine ⟨1004462473466340984092311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1339283297955121312123081 1004462473466340984092311)
        ·
          refine ⟨1506693710199511476138467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1004462473466340984092311 1506693710199511476138467)
          ·
            refine ⟨2260040565299267214207701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1506693710199511476138467 2260040565299267214207701)
            ·
              refine ⟨52969700749201575332993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2260040565299267214207701 52969700749201575332993)
              ·
                rfl

theorem cell19_522238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 7].length) (baseStart_522238 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_522238 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_522238 prefixEnd_522238 := by exact prefixLift 522238
  have htrace : WordTrace (prefixWord ++ tailWord_522238) baseStart_522238 baseEnd_522238 := by
    simpa [prefixWord, tailWord_522238, baseEnd_522238] using wordTrace_append hprefix tailTrace_522238
  have hstable : (prefixWord ++ tailWord_522238).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522238).length < 2 ^ (prefixWord ++ tailWord_522238).sum := by decide
  have hdescent : baseEnd_522238 < baseStart_522238 := by decide
  rcases family_descends (prefixWord ++ tailWord_522238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522297 : List Nat := [1, 2, 1, 5, 3, 7]
def baseStart_522297 : Nat := 118140960795 + 522297 * 2 ^ 59
def prefixEnd_522297 : Nat := 4983230072969 + 3 ^ 40 * 522297 * 2
def baseEnd_522297 : Nat := 17658561672523341187523

theorem tailTrace_522297 : CollatzResearch.WordTrace tailWord_522297 prefixEnd_522297 17658561672523341187523 := by
  unfold tailWord_522297
  simp only [CollatzResearch.WordTrace]
  refine ⟨19049736588814645071037145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12699824392543096714024763 19049736588814645071037145)
  ·
    refine ⟨14287302441610983803277859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19049736588814645071037145 14287302441610983803277859)
    ·
      refine ⟨21430953662416475704916789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14287302441610983803277859 21430953662416475704916789)
      ·
        refine ⟨2009151905851544597335949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 21430953662416475704916789 2009151905851544597335949)
        ·
          refine ⟨753431964694329224000981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2009151905851544597335949 753431964694329224000981)
          ·
            refine ⟨17658561672523341187523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 753431964694329224000981 17658561672523341187523)
            ·
              rfl

theorem cell19_522297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 7].length) (baseStart_522297 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_522297 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_522297 prefixEnd_522297 := by exact prefixLift 522297
  have htrace : WordTrace (prefixWord ++ tailWord_522297) baseStart_522297 baseEnd_522297 := by
    simpa [prefixWord, tailWord_522297, baseEnd_522297] using wordTrace_append hprefix tailTrace_522297
  have hstable : (prefixWord ++ tailWord_522297).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522297).length < 2 ^ (prefixWord ++ tailWord_522297).sum := by decide
  have hdescent : baseEnd_522297 < baseStart_522297 := by decide
  rcases family_descends (prefixWord ++ tailWord_522297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522316 : List Nat := [2, 2, 1, 3, 1, 1, 5, 4]
def baseStart_522316 : Nat := 118140960795 + 522316 * 2 ^ 59
def prefixEnd_522316 : Nat := 4983230072969 + 3 ^ 40 * 522316 * 2
def baseEnd_522316 : Nat := 158932836464523656265433

theorem tailTrace_522316 : CollatzResearch.WordTrace tailWord_522316 prefixEnd_522316 158932836464523656265433 := by
  unfold tailWord_522316
  simp only [CollatzResearch.WordTrace]
  refine ⟨9525214787872905657989401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12700286383830540877319201 9525214787872905657989401)
  ·
    refine ⟨7143911090904679243492051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9525214787872905657989401 7143911090904679243492051)
    ·
      refine ⟨10715866636357018865238077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7143911090904679243492051 10715866636357018865238077)
      ·
        refine ⟨4018449988633882074464279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10715866636357018865238077 4018449988633882074464279)
        ·
          refine ⟨6027674982950823111696419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4018449988633882074464279 6027674982950823111696419)
          ·
            refine ⟨9041512474426234667544629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6027674982950823111696419 9041512474426234667544629)
            ·
              refine ⟨847641794477459500082309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9041512474426234667544629 847641794477459500082309)
              ·
                refine ⟨158932836464523656265433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 847641794477459500082309 158932836464523656265433)
                ·
                  rfl

theorem cell19_522316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 5, 4].length) (baseStart_522316 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_522316 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_522316 prefixEnd_522316 := by exact prefixLift 522316
  have htrace : WordTrace (prefixWord ++ tailWord_522316) baseStart_522316 baseEnd_522316 := by
    simpa [prefixWord, tailWord_522316, baseEnd_522316] using wordTrace_append hprefix tailTrace_522316
  have hstable : (prefixWord ++ tailWord_522316).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522316).length < 2 ^ (prefixWord ++ tailWord_522316).sum := by decide
  have hdescent : baseEnd_522316 < baseStart_522316 := by decide
  rcases family_descends (prefixWord ++ tailWord_522316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522354 : List Nat := [3, 2, 1, 2, 2, 3, 6]
def baseStart_522354 : Nat := 118140960795 + 522354 * 2 ^ 59
def prefixEnd_522354 : Nat := 4983230072969 + 3 ^ 40 * 522354 * 2
def baseEnd_522354 : Nat := 52981466429383609140295

theorem tailTrace_522354 : CollatzResearch.WordTrace tailWord_522354 prefixEnd_522354 52981466429383609140295 := by
  unfold tailWord_522354
  simp only [CollatzResearch.WordTrace]
  refine ⟨4762953887402035951465529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12701210366405429203908077 4762953887402035951465529)
  ·
    refine ⟨3572215415551526963599147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4762953887402035951465529 3572215415551526963599147)
    ·
      refine ⟨5358323123327290445398721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3572215415551526963599147 5358323123327290445398721)
      ·
        refine ⟨4018742342495467834049041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5358323123327290445398721 4018742342495467834049041)
        ·
          refine ⟨3014056756871600875536781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4018742342495467834049041 3014056756871600875536781)
          ·
            refine ⟨1130271283826850328326293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3014056756871600875536781 1130271283826850328326293)
            ·
              refine ⟨52981466429383609140295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1130271283826850328326293 52981466429383609140295)
              ·
                rfl

theorem cell19_522354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 6].length) (baseStart_522354 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_522354 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_522354 prefixEnd_522354 := by exact prefixLift 522354
  have htrace : WordTrace (prefixWord ++ tailWord_522354) baseStart_522354 baseEnd_522354 := by
    simpa [prefixWord, tailWord_522354, baseEnd_522354] using wordTrace_append hprefix tailTrace_522354
  have hstable : (prefixWord ++ tailWord_522354).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522354).length < 2 ^ (prefixWord ++ tailWord_522354).sum := by decide
  have hdescent : baseEnd_522354 < baseStart_522354 := by decide
  rcases family_descends (prefixWord ++ tailWord_522354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522388 : List Nat := [2, 4, 2, 3, 1, 1, 1, 5]
def baseStart_522388 : Nat := 118140960795 + 522388 * 2 ^ 59
def prefixEnd_522388 : Nat := 4983230072969 + 3 ^ 40 * 522388 * 2
def baseEnd_522388 : Nat := 158954744972448822665237

theorem tailTrace_522388 : CollatzResearch.WordTrace tailWord_522388 prefixEnd_522388 158954744972448822665237 := by
  unfold tailWord_522388
  simp only [CollatzResearch.WordTrace]
  refine ⟨9526527815742483806299909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12702037087656645075066545 9526527815742483806299909)
  ·
    refine ⟨1786223965451715713681233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9526527815742483806299909 1786223965451715713681233)
    ·
      refine ⟨1339667974088786785260925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1786223965451715713681233 1339667974088786785260925)
      ·
        refine ⟨502375490283295044472847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1339667974088786785260925 502375490283295044472847)
        ·
          refine ⟨753563235424942566709271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 502375490283295044472847 753563235424942566709271)
          ·
            refine ⟨1130344853137413850063907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 753563235424942566709271 1130344853137413850063907)
            ·
              refine ⟨1695517279706120775095861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1130344853137413850063907 1695517279706120775095861)
              ·
                refine ⟨158954744972448822665237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1695517279706120775095861 158954744972448822665237)
                ·
                  rfl

theorem cell19_522388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 1, 5].length) (baseStart_522388 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_522388 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_522388 prefixEnd_522388 := by exact prefixLift 522388
  have htrace : WordTrace (prefixWord ++ tailWord_522388) baseStart_522388 baseEnd_522388 := by
    simpa [prefixWord, tailWord_522388, baseEnd_522388] using wordTrace_append hprefix tailTrace_522388
  have hstable : (prefixWord ++ tailWord_522388).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522388).length < 2 ^ (prefixWord ++ tailWord_522388).sum := by decide
  have hdescent : baseEnd_522388 < baseStart_522388 := by decide
  rcases family_descends (prefixWord ++ tailWord_522388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522407 : List Nat := [1, 1, 6, 2, 3, 1, 5]
def baseStart_522407 : Nat := 118140960795 + 522407 * 2 ^ 59
def prefixEnd_522407 : Nat := 4983230072969 + 3 ^ 40 * 522407 * 2
def baseEnd_522407 : Nat := 52986842128087469414321

theorem tailTrace_522407 : CollatzResearch.WordTrace tailWord_522407 prefixEnd_522407 52986842128087469414321 := by
  unfold tailWord_522407
  simp only [CollatzResearch.WordTrace]
  refine ⟨19053748618416133857541475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12702499078944089238360983 19053748618416133857541475)
  ·
    refine ⟨28580622927624200786312213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19053748618416133857541475 28580622927624200786312213)
    ·
      refine ⟨1339716699732384411858385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 28580622927624200786312213 1339716699732384411858385)
      ·
        refine ⟨1004787524799288308893789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1339716699732384411858385 1004787524799288308893789)
        ·
          refine ⟨376795321799733115835171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1004787524799288308893789 376795321799733115835171)
          ·
            refine ⟨565192982699599673752757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 376795321799733115835171 565192982699599673752757)
            ·
              refine ⟨52986842128087469414321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 565192982699599673752757 52986842128087469414321)
              ·
                rfl

theorem cell19_522407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 5].length) (baseStart_522407 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_522407 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_522407 prefixEnd_522407 := by exact prefixLift 522407
  have htrace : WordTrace (prefixWord ++ tailWord_522407) baseStart_522407 baseEnd_522407 := by
    simpa [prefixWord, tailWord_522407, baseEnd_522407] using wordTrace_append hprefix tailTrace_522407
  have hstable : (prefixWord ++ tailWord_522407).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522407).length < 2 ^ (prefixWord ++ tailWord_522407).sum := by decide
  have hdescent : baseEnd_522407 < baseStart_522407 := by decide
  rcases family_descends (prefixWord ++ tailWord_522407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522428 : List Nat := [2, 2, 2, 3, 3, 1, 2, 4]
def baseStart_522428 : Nat := 118140960795 + 522428 * 2 ^ 59
def prefixEnd_522428 : Nat := 4983230072969 + 3 ^ 40 * 522428 * 2
def baseEnd_522428 : Nat := 158966916365740581776239

theorem tailTrace_522428 : CollatzResearch.WordTrace tailWord_522428 prefixEnd_522428 158966916365740581776239 := by
  unfold tailWord_522428
  simp only [CollatzResearch.WordTrace]
  refine ⟨9527257275670027222027969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12703009700893369629370625 9527257275670027222027969)
  ·
    refine ⟨7145442956752520416520977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9527257275670027222027969 7145442956752520416520977)
    ·
      refine ⟨5359082217564390312390733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7145442956752520416520977 5359082217564390312390733)
      ·
        refine ⟨2009655831586646367146525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5359082217564390312390733 2009655831586646367146525)
        ·
          refine ⟨753620936844992387679947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2009655831586646367146525 753620936844992387679947)
          ·
            refine ⟨1130431405267488581519921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 753620936844992387679947 1130431405267488581519921)
            ·
              refine ⟨847823553950616436139941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1130431405267488581519921 847823553950616436139941)
              ·
                refine ⟨158966916365740581776239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 847823553950616436139941 158966916365740581776239)
                ·
                  rfl

theorem cell19_522428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 2, 4].length) (baseStart_522428 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_522428 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_522428 prefixEnd_522428 := by exact prefixLift 522428
  have htrace : WordTrace (prefixWord ++ tailWord_522428) baseStart_522428 baseEnd_522428 := by
    simpa [prefixWord, tailWord_522428, baseEnd_522428] using wordTrace_append hprefix tailTrace_522428
  have hstable : (prefixWord ++ tailWord_522428).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522428).length < 2 ^ (prefixWord ++ tailWord_522428).sum := by decide
  have hdescent : baseEnd_522428 < baseStart_522428 := by decide
  rcases family_descends (prefixWord ++ tailWord_522428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522489 : List Nat := [1, 2, 1, 3, 1, 1, 2, 8]
def baseStart_522489 : Nat := 118140960795 + 522489 * 2 ^ 59
def prefixEnd_522489 : Nat := 4983230072969 + 3 ^ 40 * 522489 * 2
def baseEnd_522489 : Nat := 158985477740510514420517

theorem tailTrace_522489 : CollatzResearch.WordTrace tailWord_522489 prefixEnd_522489 158985477740510514420517 := by
  unfold tailWord_522489
  simp only [CollatzResearch.WordTrace]
  refine ⟨19056739404119061862026521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12704492936079374574684347 19056739404119061862026521)
  ·
    refine ⟨14292554553089296396519891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19056739404119061862026521 14292554553089296396519891)
    ·
      refine ⟨21438831829633944594779837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14292554553089296396519891 21438831829633944594779837)
      ·
        refine ⟨8039561936112729223042439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21438831829633944594779837 8039561936112729223042439)
        ·
          refine ⟨12059342904169093834563659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8039561936112729223042439 12059342904169093834563659)
          ·
            refine ⟨18089014356253640751845489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12059342904169093834563659 18089014356253640751845489)
            ·
              refine ⟨13566760767190230563884117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18089014356253640751845489 13566760767190230563884117)
              ·
                refine ⟨158985477740510514420517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13566760767190230563884117 158985477740510514420517)
                ·
                  rfl

theorem cell19_522489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 8].length) (baseStart_522489 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_522489 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_522489 prefixEnd_522489 := by exact prefixLift 522489
  have htrace : WordTrace (prefixWord ++ tailWord_522489) baseStart_522489 baseEnd_522489 := by
    simpa [prefixWord, tailWord_522489, baseEnd_522489] using wordTrace_append hprefix tailTrace_522489
  have hstable : (prefixWord ++ tailWord_522489).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522489).length < 2 ^ (prefixWord ++ tailWord_522489).sum := by decide
  have hdescent : baseEnd_522489 < baseStart_522489 := by decide
  rcases family_descends (prefixWord ++ tailWord_522489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522504 : List Nat := [2, 1, 3, 2, 3, 2, 3, 3]
def baseStart_522504 : Nat := 118140960795 + 522504 * 2 ^ 59
def prefixEnd_522504 : Nat := 4983230072969 + 3 ^ 40 * 522504 * 2
def baseEnd_522504 : Nat := 158990042012994924087143

theorem tailTrace_522504 : CollatzResearch.WordTrace tailWord_522504 prefixEnd_522504 158990042012994924087143 := by
  unfold tailWord_522504
  simp only [CollatzResearch.WordTrace]
  refine ⟨9528643249532359711911283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12704857666043146282548377 9528643249532359711911283)
  ·
    refine ⟨14292964874298539567866925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9528643249532359711911283 14292964874298539567866925)
    ·
      refine ⟨5359861827861952337950097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14292964874298539567866925 5359861827861952337950097)
      ·
        refine ⟨4019896370896464253462573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5359861827861952337950097 4019896370896464253462573)
        ·
          refine ⟨1507461139086174095048465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4019896370896464253462573 1507461139086174095048465)
          ·
            refine ⟨1130595854314630571286349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1507461139086174095048465 1130595854314630571286349)
            ·
              refine ⟨423973445367986464232381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1130595854314630571286349 423973445367986464232381)
              ·
                refine ⟨158990042012994924087143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 423973445367986464232381 158990042012994924087143)
                ·
                  rfl

theorem cell19_522504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 3, 3].length) (baseStart_522504 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_522504 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_522504 prefixEnd_522504 := by exact prefixLift 522504
  have htrace : WordTrace (prefixWord ++ tailWord_522504) baseStart_522504 baseEnd_522504 := by
    simpa [prefixWord, tailWord_522504, baseEnd_522504] using wordTrace_append hprefix tailTrace_522504
  have hstable : (prefixWord ++ tailWord_522504).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522504).length < 2 ^ (prefixWord ++ tailWord_522504).sum := by decide
  have hdescent : baseEnd_522504 < baseStart_522504 := by decide
  rcases family_descends (prefixWord ++ tailWord_522504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522561 : List Nat := [1, 2, 5, 2, 2, 1, 1, 5]
def baseStart_522561 : Nat := 118140960795 + 522561 * 2 ^ 59
def prefixEnd_522561 : Nat := 4983230072969 + 3 ^ 40 * 522561 * 2
def baseEnd_522561 : Nat := 159007386248435680820321

theorem tailTrace_522561 : CollatzResearch.WordTrace tailWord_522561 prefixEnd_522561 159007386248435680820321 := by
  unfold tailWord_522561
  simp only [CollatzResearch.WordTrace]
  refine ⟨19059365459858218158647537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12706243639905478772431691 19059365459858218158647537)
  ·
    refine ⟨14294524094893663618985653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19059365459858218158647537 14294524094893663618985653)
    ·
      refine ⟨1340111633896280964279905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14294524094893663618985653 1340111633896280964279905)
      ·
        refine ⟨1005083725422210723209929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1340111633896280964279905 1005083725422210723209929)
        ·
          refine ⟨753812794066658042407447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1005083725422210723209929 753812794066658042407447)
          ·
            refine ⟨1130719191099987063611171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 753812794066658042407447 1130719191099987063611171)
            ·
              refine ⟨1696078786649980595416757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1130719191099987063611171 1696078786649980595416757)
              ·
                refine ⟨159007386248435680820321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1696078786649980595416757 159007386248435680820321)
                ·
                  rfl

theorem cell19_522561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 1, 5].length) (baseStart_522561 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_522561 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_522561 prefixEnd_522561 := by exact prefixLift 522561
  have htrace : WordTrace (prefixWord ++ tailWord_522561) baseStart_522561 baseEnd_522561 := by
    simpa [prefixWord, tailWord_522561, baseEnd_522561] using wordTrace_append hprefix tailTrace_522561
  have hstable : (prefixWord ++ tailWord_522561).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522561).length < 2 ^ (prefixWord ++ tailWord_522561).sum := by decide
  have hdescent : baseEnd_522561 < baseStart_522561 := by decide
  rcases family_descends (prefixWord ++ tailWord_522561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522563 : List Nat := [1, 1, 1, 3, 1, 3, 6, 3]
def baseStart_522563 : Nat := 118140960795 + 522563 * 2 ^ 59
def prefixEnd_522563 : Nat := 4983230072969 + 3 ^ 40 * 522563 * 2
def baseEnd_522563 : Nat := 159007994818100268775871

theorem tailTrace_522563 : CollatzResearch.WordTrace tailWord_522563 prefixEnd_522563 159007994818100268775871 := by
  unfold tailWord_522563
  simp only [CollatzResearch.WordTrace]
  refine ⟨19059438405850972500220343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12706292270567315000146895 19059438405850972500220343)
  ·
    refine ⟨28589157608776458750330515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19059438405850972500220343 28589157608776458750330515)
    ·
      refine ⟨42883736413164688125495773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28589157608776458750330515 42883736413164688125495773)
      ·
        refine ⟨16081401154936758047060915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42883736413164688125495773 16081401154936758047060915)
        ·
          refine ⟨24122101732405137070591373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16081401154936758047060915 24122101732405137070591373)
          ·
            refine ⟨9045788149651926401471765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24122101732405137070591373 9045788149651926401471765)
            ·
              refine ⟨424021319514934050068989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 9045788149651926401471765 424021319514934050068989)
              ·
                refine ⟨159007994818100268775871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 424021319514934050068989 159007994818100268775871)
                ·
                  rfl

theorem cell19_522563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 6, 3].length) (baseStart_522563 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_522563 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_522563 prefixEnd_522563 := by exact prefixLift 522563
  have htrace : WordTrace (prefixWord ++ tailWord_522563) baseStart_522563 baseEnd_522563 := by
    simpa [prefixWord, tailWord_522563, baseEnd_522563] using wordTrace_append hprefix tailTrace_522563
  have hstable : (prefixWord ++ tailWord_522563).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522563).length < 2 ^ (prefixWord ++ tailWord_522563).sum := by decide
  have hdescent : baseEnd_522563 < baseStart_522563 := by decide
  rcases family_descends (prefixWord ++ tailWord_522563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522654 : List Nat := [4, 3, 1, 2, 1, 3, 1, 4]
def baseStart_522654 : Nat := 118140960795 + 522654 * 2 ^ 59
def prefixEnd_522654 : Nat := 4983230072969 + 3 ^ 40 * 522654 * 2
def baseEnd_522654 : Nat := 159035684737839020753401

theorem tailTrace_522654 : CollatzResearch.WordTrace tailWord_522654 prefixEnd_522654 159035684737839020753401 := by
  unfold tailWord_522654
  simp only [CollatzResearch.WordTrace]
  refine ⟨2382844681065161880222877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12708504965680863361188677 2382844681065161880222877)
  ·
    refine ⟨893566755399435705083579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2382844681065161880222877 893566755399435705083579)
    ·
      refine ⟨1340350133099153557625369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 893566755399435705083579 1340350133099153557625369)
      ·
        refine ⟨1005262599824365168219027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1340350133099153557625369 1005262599824365168219027)
        ·
          refine ⟨1507893899736547752328541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1005262599824365168219027 1507893899736547752328541)
          ·
            refine ⟨565460212401205407123203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1507893899736547752328541 565460212401205407123203)
            ·
              refine ⟨848190318601808110684805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 565460212401205407123203 848190318601808110684805)
              ·
                refine ⟨159035684737839020753401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 848190318601808110684805 159035684737839020753401)
                ·
                  rfl

theorem cell19_522654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 1, 4].length) (baseStart_522654 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_522654 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_522654 prefixEnd_522654 := by exact prefixLift 522654
  have htrace : WordTrace (prefixWord ++ tailWord_522654) baseStart_522654 baseEnd_522654 := by
    simpa [prefixWord, tailWord_522654, baseEnd_522654] using wordTrace_append hprefix tailTrace_522654
  have hstable : (prefixWord ++ tailWord_522654).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522654).length < 2 ^ (prefixWord ++ tailWord_522654).sum := by decide
  have hdescent : baseEnd_522654 < baseStart_522654 := by decide
  rcases family_descends (prefixWord ++ tailWord_522654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522698 : List Nat := [3, 1, 2, 1, 2, 2, 8]
def baseStart_522698 : Nat := 118140960795 + 522698 * 2 ^ 59
def prefixEnd_522698 : Nat := 4983230072969 + 3 ^ 40 * 522698 * 2
def baseEnd_522698 : Nat := 53016357756819985258501

theorem tailTrace_522698 : CollatzResearch.WordTrace tailWord_522698 prefixEnd_522698 53016357756819985258501 := by
  unfold tailWord_522698
  simp only [CollatzResearch.WordTrace]
  refine ⟨4766090565090472639096187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12709574840241260370923165 4766090565090472639096187)
  ·
    refine ⟨7149135847635708958644281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4766090565090472639096187 7149135847635708958644281)
    ·
      refine ⟨5361851885726781718983211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7149135847635708958644281 5361851885726781718983211)
      ·
        refine ⟨8042777828590172578474817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5361851885726781718983211 8042777828590172578474817)
        ·
          refine ⟨6032083371442629433856113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8042777828590172578474817 6032083371442629433856113)
          ·
            refine ⟨4524062528581972075392085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6032083371442629433856113 4524062528581972075392085)
            ·
              refine ⟨53016357756819985258501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4524062528581972075392085 53016357756819985258501)
              ·
                rfl

theorem cell19_522698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 8].length) (baseStart_522698 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_522698 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_522698 prefixEnd_522698 := by exact prefixLift 522698
  have htrace : WordTrace (prefixWord ++ tailWord_522698) baseStart_522698 baseEnd_522698 := by
    simpa [prefixWord, tailWord_522698, baseEnd_522698] using wordTrace_append hprefix tailTrace_522698
  have hstable : (prefixWord ++ tailWord_522698).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522698).length < 2 ^ (prefixWord ++ tailWord_522698).sum := by decide
  have hdescent : baseEnd_522698 < baseStart_522698 := by decide
  rcases family_descends (prefixWord ++ tailWord_522698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522734 : List Nat := [4, 1, 2, 1, 2, 3, 1, 5]
def baseStart_522734 : Nat := 118140960795 + 522734 * 2 ^ 59
def prefixEnd_522734 : Nat := 4983230072969 + 3 ^ 40 * 522734 * 2
def baseEnd_522734 : Nat := 159060027524422538975405

theorem tailTrace_522734 : CollatzResearch.WordTrace tailWord_522734 prefixEnd_522734 159060027524422538975405 := by
  unfold tailWord_522734
  simp only [CollatzResearch.WordTrace]
  refine ⟨2383209411028933588086907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12710450192154312469796837 2383209411028933588086907)
  ·
    refine ⟨3574814116543400382130361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2383209411028933588086907 3574814116543400382130361)
    ·
      refine ⟨2681110587407550286597771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3574814116543400382130361 2681110587407550286597771)
      ·
        refine ⟨4021665881111325429896657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2681110587407550286597771 4021665881111325429896657)
        ·
          refine ⟨3016249410833494072422493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4021665881111325429896657 3016249410833494072422493)
          ·
            refine ⟨1131093529062560277158435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3016249410833494072422493 1131093529062560277158435)
            ·
              refine ⟨1696640293593840415737653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1131093529062560277158435 1696640293593840415737653)
              ·
                refine ⟨159060027524422538975405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1696640293593840415737653 159060027524422538975405)
                ·
                  rfl

theorem cell19_522734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 1, 5].length) (baseStart_522734 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_522734 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_522734 prefixEnd_522734 := by exact prefixLift 522734
  have htrace : WordTrace (prefixWord ++ tailWord_522734) baseStart_522734 baseEnd_522734 := by
    simpa [prefixWord, tailWord_522734, baseEnd_522734] using wordTrace_append hprefix tailTrace_522734
  have hstable : (prefixWord ++ tailWord_522734).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522734).length < 2 ^ (prefixWord ++ tailWord_522734).sum := by decide
  have hdescent : baseEnd_522734 < baseStart_522734 := by decide
  rcases family_descends (prefixWord ++ tailWord_522734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522736 : List Nat := [2, 1, 1, 1, 3, 3, 3, 5]
def baseStart_522736 : Nat := 118140960795 + 522736 * 2 ^ 59
def prefixEnd_522736 : Nat := 4983230072969 + 3 ^ 40 * 522736 * 2
def baseEnd_522736 : Nat := 159060636094087126930955

theorem tailTrace_522736 : CollatzResearch.WordTrace tailWord_522736 prefixEnd_522736 159060636094087126930955 := by
  unfold tailWord_522736
  simp only [CollatzResearch.WordTrace]
  refine ⟨9532874117112111523134031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12710498822816148697512041 9532874117112111523134031)
  ·
    refine ⟨14299311175668167284701047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9532874117112111523134031 14299311175668167284701047)
    ·
      refine ⟨21448966763502250927051571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14299311175668167284701047 21448966763502250927051571)
      ·
        refine ⟨32173450145253376390577357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21448966763502250927051571 32173450145253376390577357)
        ·
          refine ⟨12065043804470016146466509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32173450145253376390577357 12065043804470016146466509)
          ·
            refine ⟨4524391426676256054924941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12065043804470016146466509 4524391426676256054924941)
            ·
              refine ⟨1696646785003596020596853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4524391426676256054924941 1696646785003596020596853)
              ·
                refine ⟨159060636094087126930955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1696646785003596020596853 159060636094087126930955)
                ·
                  rfl

theorem cell19_522736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 3, 5].length) (baseStart_522736 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_522736 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_522736 prefixEnd_522736 := by exact prefixLift 522736
  have htrace : WordTrace (prefixWord ++ tailWord_522736) baseStart_522736 baseEnd_522736 := by
    simpa [prefixWord, tailWord_522736, baseEnd_522736] using wordTrace_append hprefix tailTrace_522736
  have hstable : (prefixWord ++ tailWord_522736).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522736).length < 2 ^ (prefixWord ++ tailWord_522736).sum := by decide
  have hdescent : baseEnd_522736 < baseStart_522736 := by decide
  rcases family_descends (prefixWord ++ tailWord_522736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522753 : List Nat := [1, 2, 4, 1, 3, 3, 5]
def baseStart_522753 : Nat := 118140960795 + 522753 * 2 ^ 59
def prefixEnd_522753 : Nat := 4983230072969 + 3 ^ 40 * 522753 * 2
def baseEnd_522753 : Nat := 53021936312078708184377

theorem tailTrace_522753 : CollatzResearch.WordTrace tailWord_522753 prefixEnd_522753 53021936312078708184377 := by
  unfold tailWord_522753
  simp only [CollatzResearch.WordTrace]
  refine ⟨19066368275162634949636913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12710912183441756633091275 19066368275162634949636913)
  ·
    refine ⟨14299776206371976212227685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19066368275162634949636913 14299776206371976212227685)
    ·
      refine ⟨2681208038694745539792691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14299776206371976212227685 2681208038694745539792691)
      ·
        refine ⟨4021812058042118309689037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2681208038694745539792691 4021812058042118309689037)
        ·
          refine ⟨1508179521765794366133389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4021812058042118309689037 1508179521765794366133389)
          ·
            refine ⟨565567320662172887300021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1508179521765794366133389 565567320662172887300021)
            ·
              refine ⟨53021936312078708184377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 565567320662172887300021 53021936312078708184377)
              ·
                rfl

theorem cell19_522753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 5].length) (baseStart_522753 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_522753 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_522753 prefixEnd_522753 := by exact prefixLift 522753
  have htrace : WordTrace (prefixWord ++ tailWord_522753) baseStart_522753 baseEnd_522753 := by
    simpa [prefixWord, tailWord_522753, baseEnd_522753] using wordTrace_append hprefix tailTrace_522753
  have hstable : (prefixWord ++ tailWord_522753).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522753).length < 2 ^ (prefixWord ++ tailWord_522753).sum := by decide
  have hdescent : baseEnd_522753 < baseStart_522753 := by decide
  rcases family_descends (prefixWord ++ tailWord_522753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522812 : List Nat := [2, 2, 2, 2, 3, 8]
def baseStart_522812 : Nat := 118140960795 + 522812 * 2 ^ 59
def prefixEnd_522812 : Nat := 4983230072969 + 3 ^ 40 * 522812 * 2
def baseEnd_522812 : Nat := 17675973526815718804651

theorem tailTrace_522812 : CollatzResearch.WordTrace tailWord_522812 prefixEnd_522812 17675973526815718804651 := by
  unfold tailWord_522812
  simp only [CollatzResearch.WordTrace]
  refine ⟨9534260090974444013017345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12712346787965925350689793 9534260090974444013017345)
  ·
    refine ⟨7150695068230833009763009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9534260090974444013017345 7150695068230833009763009)
    ·
      refine ⟨5363021301173124757322257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7150695068230833009763009 5363021301173124757322257)
      ·
        refine ⟨4022265975879843567991693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5363021301173124757322257 4022265975879843567991693)
        ·
          refine ⟨1508349740954941337996885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4022265975879843567991693 1508349740954941337996885)
          ·
            refine ⟨17675973526815718804651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1508349740954941337996885 17675973526815718804651)
            ·
              rfl

theorem cell19_522812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 8].length) (baseStart_522812 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_522812 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_522812 prefixEnd_522812 := by exact prefixLift 522812
  have htrace : WordTrace (prefixWord ++ tailWord_522812) baseStart_522812 baseEnd_522812 := by
    simpa [prefixWord, tailWord_522812, baseEnd_522812] using wordTrace_append hprefix tailTrace_522812
  have hstable : (prefixWord ++ tailWord_522812).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522812).length < 2 ^ (prefixWord ++ tailWord_522812).sum := by decide
  have hdescent : baseEnd_522812 < baseStart_522812 := by decide
  rcases family_descends (prefixWord ++ tailWord_522812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522831 : List Nat := [1, 1, 2, 1, 1, 2, 7, 4]
def baseStart_522831 : Nat := 118140960795 + 522831 * 2 ^ 59
def prefixEnd_522831 : Nat := 4983230072969 + 3 ^ 40 * 522831 * 2
def baseEnd_522831 : Nat := 159089543153155054819585

theorem tailTrace_522831 : CollatzResearch.WordTrace tailWord_522831 prefixEnd_522831 159089543153155054819585 := by
  unfold tailWord_522831
  simp only [CollatzResearch.WordTrace]
  refine ⟨19069213168880054270976347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12712808779253369513984231 19069213168880054270976347)
  ·
    refine ⟨28603819753320081406464521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19069213168880054270976347 28603819753320081406464521)
    ·
      refine ⟨21452864814990061054848391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28603819753320081406464521 21452864814990061054848391)
      ·
        refine ⟨32179297222485091582272587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21452864814990061054848391 32179297222485091582272587)
        ·
          refine ⟨48268945833727637373408881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32179297222485091582272587 48268945833727637373408881)
          ·
            refine ⟨36201709375295728030056661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48268945833727637373408881 36201709375295728030056661)
            ·
              refine ⟨848477563483493625704453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 36201709375295728030056661 848477563483493625704453)
              ·
                refine ⟨159089543153155054819585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 848477563483493625704453 159089543153155054819585)
                ·
                  rfl

theorem cell19_522831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 7, 4].length) (baseStart_522831 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_522831 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_522831 prefixEnd_522831 := by exact prefixLift 522831
  have htrace : WordTrace (prefixWord ++ tailWord_522831) baseStart_522831 baseEnd_522831 := by
    simpa [prefixWord, tailWord_522831, baseEnd_522831] using wordTrace_append hprefix tailTrace_522831
  have hstable : (prefixWord ++ tailWord_522831).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522831).length < 2 ^ (prefixWord ++ tailWord_522831).sum := by decide
  have hdescent : baseEnd_522831 < baseStart_522831 := by decide
  rcases family_descends (prefixWord ++ tailWord_522831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_523002 : List Nat := [3, 1, 1, 1, 1, 3, 5, 4]
def baseStart_523002 : Nat := 118140960795 + 523002 * 2 ^ 59
def prefixEnd_523002 : Nat := 4983230072969 + 3 ^ 40 * 523002 * 2
def baseEnd_523002 : Nat := 159141575859477325019119

theorem tailTrace_523002 : CollatzResearch.WordTrace tailWord_523002 prefixEnd_523002 159141575859477325019119 := by
  unfold tailWord_523002
  simp only [CollatzResearch.WordTrace]
  refine ⟨4768862512815137618862815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12716966700840366983634173 4768862512815137618862815)
  ·
    refine ⟨7153293769222706428294223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4768862512815137618862815 7153293769222706428294223)
    ·
      refine ⟨10729940653834059642441335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7153293769222706428294223 10729940653834059642441335)
      ·
        refine ⟨16094910980751089463662003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10729940653834059642441335 16094910980751089463662003)
        ·
          refine ⟨24142366471126634195493005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16094910980751089463662003 24142366471126634195493005)
          ·
            refine ⟨9053387426672487823309877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24142366471126634195493005 9053387426672487823309877)
            ·
              refine ⟨848755071250545733435301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9053387426672487823309877 848755071250545733435301)
              ·
                refine ⟨159141575859477325019119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 848755071250545733435301 159141575859477325019119)
                ·
                  rfl

theorem cell19_523002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 5, 4].length) (baseStart_523002 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_523002 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_523002 prefixEnd_523002 := by exact prefixLift 523002
  have htrace : WordTrace (prefixWord ++ tailWord_523002) baseStart_523002 baseEnd_523002 := by
    simpa [prefixWord, tailWord_523002, baseEnd_523002] using wordTrace_append hprefix tailTrace_523002
  have hstable : (prefixWord ++ tailWord_523002).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523002).length < 2 ^ (prefixWord ++ tailWord_523002).sum := by decide
  have hdescent : baseEnd_523002 < baseStart_523002 := by decide
  rcases family_descends (prefixWord ++ tailWord_523002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_523040 : List Nat := [2, 1, 1, 5, 1, 3, 6]
def baseStart_523040 : Nat := 118140960795 + 523040 * 2 ^ 59
def prefixEnd_523040 : Nat := 4983230072969 + 3 ^ 40 * 523040 * 2
def baseEnd_523040 : Nat := 53051046227701498724857

theorem tailTrace_523040 : CollatzResearch.WordTrace tailWord_523040 prefixEnd_523040 53051046227701498724857 := by
  unfold tailWord_523040
  simp only [CollatzResearch.WordTrace]
  refine ⟨9538418012561441482667287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12717890683415255310223049 9538418012561441482667287)
  ·
    refine ⟨14307627018842162224000931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9538418012561441482667287 14307627018842162224000931)
    ·
      refine ⟨21461440528263243336001397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14307627018842162224000931 21461440528263243336001397)
      ·
        refine ⟨2012010049524679062750131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 21461440528263243336001397 2012010049524679062750131)
        ·
          refine ⟨3018015074287018594125197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2012010049524679062750131 3018015074287018594125197)
          ·
            refine ⟨1131755652857631972796949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3018015074287018594125197 1131755652857631972796949)
            ·
              refine ⟨53051046227701498724857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1131755652857631972796949 53051046227701498724857)
              ·
                rfl

theorem cell19_523040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 6].length) (baseStart_523040 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_523040 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_523040 prefixEnd_523040 := by exact prefixLift 523040
  have htrace : WordTrace (prefixWord ++ tailWord_523040) baseStart_523040 baseEnd_523040 := by
    simpa [prefixWord, tailWord_523040, baseEnd_523040] using wordTrace_append hprefix tailTrace_523040
  have hstable : (prefixWord ++ tailWord_523040).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523040).length < 2 ^ (prefixWord ++ tailWord_523040).sum := by decide
  have hdescent : baseEnd_523040 < baseStart_523040 := by decide
  rcases family_descends (prefixWord ++ tailWord_523040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_523097 : List Nat := [1, 2, 1, 2, 2, 6, 5]
def baseStart_523097 : Nat := 118140960795 + 523097 * 2 ^ 59
def prefixEnd_523097 : Nat := 4983230072969 + 3 ^ 40 * 523097 * 2
def baseEnd_523097 : Nat := 53056827639515084302583

theorem tailTrace_523097 : CollatzResearch.WordTrace tailWord_523097 prefixEnd_523097 53056827639515084302583 := by
  unfold tailWord_523097
  simp only [CollatzResearch.WordTrace]
  refine ⟨19078914985916381700159545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12719276657277587800106363 19078914985916381700159545)
  ·
    refine ⟨14309186239437286275119659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19078914985916381700159545 14309186239437286275119659)
    ·
      refine ⟨21463779359155929412679489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14309186239437286275119659 21463779359155929412679489)
      ·
        refine ⟨16097834519366947059509617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21463779359155929412679489 16097834519366947059509617)
        ·
          refine ⟨12073375889525210294632213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16097834519366947059509617 12073375889525210294632213)
          ·
            refine ⟨565939494821494232560885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 12073375889525210294632213 565939494821494232560885)
            ·
              refine ⟨53056827639515084302583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 565939494821494232560885 53056827639515084302583)
              ·
                rfl

theorem cell19_523097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 5].length) (baseStart_523097 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_523097 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_523097 prefixEnd_523097 := by exact prefixLift 523097
  have htrace : WordTrace (prefixWord ++ tailWord_523097) baseStart_523097 baseEnd_523097 := by
    simpa [prefixWord, tailWord_523097, baseEnd_523097] using wordTrace_append hprefix tailTrace_523097
  have hstable : (prefixWord ++ tailWord_523097).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523097).length < 2 ^ (prefixWord ++ tailWord_523097).sum := by decide
  have hdescent : baseEnd_523097 < baseStart_523097 := by decide
  rcases family_descends (prefixWord ++ tailWord_523097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_523116 : List Nat := [2, 2, 1, 1, 4, 1, 4, 4]
def baseStart_523116 : Nat := 118140960795 + 523116 * 2 ^ 59
def prefixEnd_523116 : Nat := 4983230072969 + 3 ^ 40 * 523116 * 2
def baseEnd_523116 : Nat := 159176264330358838485475

theorem tailTrace_523116 : CollatzResearch.WordTrace tailWord_523116 prefixEnd_523116 159176264330358838485475 := by
  unfold tailWord_523116
  simp only [CollatzResearch.WordTrace]
  refine ⟨9539803986423773972550601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12719738648565031963400801 9539803986423773972550601)
  ·
    refine ⟨7154852989817830479412951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9539803986423773972550601 7154852989817830479412951)
    ·
      refine ⟨10732279484726745719119427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7154852989817830479412951 10732279484726745719119427)
      ·
        refine ⟨16098419227090118578679141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10732279484726745719119427 16098419227090118578679141)
        ·
          refine ⟨3018453605079397233502339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16098419227090118578679141 3018453605079397233502339)
          ·
            refine ⟨4527680407619095850253509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3018453605079397233502339 4527680407619095850253509)
            ·
              refine ⟨848940076428580471922533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4527680407619095850253509 848940076428580471922533)
              ·
                refine ⟨159176264330358838485475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 848940076428580471922533 159176264330358838485475)
                ·
                  rfl

theorem cell19_523116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 4, 4].length) (baseStart_523116 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_523116 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_523116 prefixEnd_523116 := by exact prefixLift 523116
  have htrace : WordTrace (prefixWord ++ tailWord_523116) baseStart_523116 baseEnd_523116 := by
    simpa [prefixWord, tailWord_523116, baseEnd_523116] using wordTrace_append hprefix tailTrace_523116
  have hstable : (prefixWord ++ tailWord_523116).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523116).length < 2 ^ (prefixWord ++ tailWord_523116).sum := by decide
  have hdescent : baseEnd_523116 < baseStart_523116 := by decide
  rcases family_descends (prefixWord ++ tailWord_523116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_523154 : List Nat := [3, 2, 3, 2, 9]
def baseStart_523154 : Nat := 118140960795 + 523154 * 2 ^ 59
def prefixEnd_523154 : Nat := 4983230072969 + 3 ^ 40 * 523154 * 2
def baseEnd_523154 : Nat := 5895845450147629986701

theorem tailTrace_523154 : CollatzResearch.WordTrace tailWord_523154 prefixEnd_523154 5895845450147629986701 := by
  unfold tailWord_523154
  simp only [CollatzResearch.WordTrace]
  refine ⟨4770248486677470108746129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12720662631139920289989677 4770248486677470108746129)
  ·
    refine ⟨3577686365008102581559597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4770248486677470108746129 3577686365008102581559597)
    ·
      refine ⟨1341632386878038468084849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3577686365008102581559597 1341632386878038468084849)
      ·
        refine ⟨1006224290158528851063637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1341632386878038468084849 1006224290158528851063637)
        ·
          refine ⟨5895845450147629986701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 1006224290158528851063637 5895845450147629986701)
          ·
            rfl

theorem cell19_523154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 9].length) (baseStart_523154 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_523154 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_523154 prefixEnd_523154 := by exact prefixLift 523154
  have htrace : WordTrace (prefixWord ++ tailWord_523154) baseStart_523154 baseEnd_523154 := by
    simpa [prefixWord, tailWord_523154, baseEnd_523154] using wordTrace_append hprefix tailTrace_523154
  have hstable : (prefixWord ++ tailWord_523154).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523154).length < 2 ^ (prefixWord ++ tailWord_523154).sum := by decide
  have hdescent : baseEnd_523154 < baseStart_523154 := by decide
  rcases family_descends (prefixWord ++ tailWord_523154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_523247 : List Nat := [1, 1, 2, 1, 4, 5, 2, 3]
def baseStart_523247 : Nat := 118140960795 + 523247 * 2 ^ 59
def prefixEnd_523247 : Nat := 4983230072969 + 3 ^ 40 * 523247 * 2
def baseEnd_523247 : Nat := 159216125643389349574007

theorem tailTrace_523247 : CollatzResearch.WordTrace tailWord_523247 prefixEnd_523247 159216125643389349574007 := by
  unfold tailWord_523247
  simp only [CollatzResearch.WordTrace]
  refine ⟨19084385935372957318119995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12722923956915304878746663 19084385935372957318119995)
  ·
    refine ⟨28626578903059435977179993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19084385935372957318119995 28626578903059435977179993)
    ·
      refine ⟨21469934177294576982884995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28626578903059435977179993 21469934177294576982884995)
      ·
        refine ⟨32204901265941865474327493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21469934177294576982884995 32204901265941865474327493)
        ·
          refine ⟨6038418987364099776436405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32204901265941865474327493 6038418987364099776436405)
          ·
            refine ⟨566101780065384354040913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6038418987364099776436405 566101780065384354040913)
            ·
              refine ⟨424576335049038265530685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 566101780065384354040913 424576335049038265530685)
              ·
                refine ⟨159216125643389349574007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 424576335049038265530685 159216125643389349574007)
                ·
                  rfl

theorem cell19_523247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 2, 3].length) (baseStart_523247 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_523247 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_523247 prefixEnd_523247 := by exact prefixLift 523247
  have htrace : WordTrace (prefixWord ++ tailWord_523247) baseStart_523247 baseEnd_523247 := by
    simpa [prefixWord, tailWord_523247, baseEnd_523247] using wordTrace_append hprefix tailTrace_523247
  have hstable : (prefixWord ++ tailWord_523247).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523247).length < 2 ^ (prefixWord ++ tailWord_523247).sum := by decide
  have hdescent : baseEnd_523247 < baseStart_523247 := by decide
  rcases family_descends (prefixWord ++ tailWord_523247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_523249 : List Nat := [1, 2, 2, 2, 4, 2, 1, 5]
def baseStart_523249 : Nat := 118140960795 + 523249 * 2 ^ 59
def prefixEnd_523249 : Nat := 4983230072969 + 3 ^ 40 * 523249 * 2
def baseEnd_523249 : Nat := 159216734213053937529557

theorem tailTrace_523249 : CollatzResearch.WordTrace tailWord_523249 prefixEnd_523249 159216734213053937529557 := by
  unfold tailWord_523249
  simp only [CollatzResearch.WordTrace]
  refine ⟨19084458881365711659692801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12722972587577141106461867 19084458881365711659692801)
  ·
    refine ⟨14313344161024283744769601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19084458881365711659692801 14313344161024283744769601)
    ·
      refine ⟨10735008120768212808577201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14313344161024283744769601 10735008120768212808577201)
      ·
        refine ⟨8051256090576159606432901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10735008120768212808577201 8051256090576159606432901)
        ·
          refine ⟨1509610516983029926206169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8051256090576159606432901 1509610516983029926206169)
          ·
            refine ⟨1132207887737272444654627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1509610516983029926206169 1132207887737272444654627)
            ·
              refine ⟨1698311831605908666981941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1132207887737272444654627 1698311831605908666981941)
              ·
                refine ⟨159216734213053937529557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1698311831605908666981941 159216734213053937529557)
                ·
                  rfl

theorem cell19_523249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 1, 5].length) (baseStart_523249 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_523249 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_523249 prefixEnd_523249 := by exact prefixLift 523249
  have htrace : WordTrace (prefixWord ++ tailWord_523249) baseStart_523249 baseEnd_523249 := by
    simpa [prefixWord, tailWord_523249, baseEnd_523249] using wordTrace_append hprefix tailTrace_523249
  have hstable : (prefixWord ++ tailWord_523249).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523249).length < 2 ^ (prefixWord ++ tailWord_523249).sum := by decide
  have hdescent : baseEnd_523249 < baseStart_523249 := by decide
  rcases family_descends (prefixWord ++ tailWord_523249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_523287 : List Nat := [1, 1, 3, 5, 1, 1, 1, 6]
def baseStart_523287 : Nat := 118140960795 + 523287 * 2 ^ 59
def prefixEnd_523287 : Nat := 4983230072969 + 3 ^ 40 * 523287 * 2
def baseEnd_523287 : Nat := 159228297036681108685009

theorem tailTrace_523287 : CollatzResearch.WordTrace tailWord_523287 prefixEnd_523287 159228297036681108685009 := by
  unfold tailWord_523287
  simp only [CollatzResearch.WordTrace]
  refine ⟨19085844855228044149576115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12723896570152029433050743 19085844855228044149576115)
  ·
    refine ⟨28628767282842066224364173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19085844855228044149576115 28628767282842066224364173)
    ·
      refine ⟨10735787731065774834136565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28628767282842066224364173 10735787731065774834136565)
      ·
        refine ⟨1006480099787416390700303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10735787731065774834136565 1006480099787416390700303)
        ·
          refine ⟨1509720149681124586050455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1006480099787416390700303 1509720149681124586050455)
          ·
            refine ⟨2264580224521686879075683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1509720149681124586050455 2264580224521686879075683)
            ·
              refine ⟨3396870336782530318613525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2264580224521686879075683 3396870336782530318613525)
              ·
                refine ⟨159228297036681108685009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3396870336782530318613525 159228297036681108685009)
                ·
                  rfl

theorem cell19_523287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 6].length) (baseStart_523287 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_523287 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_523287 prefixEnd_523287 := by exact prefixLift 523287
  have htrace : WordTrace (prefixWord ++ tailWord_523287) baseStart_523287 baseEnd_523287 := by
    simpa [prefixWord, tailWord_523287, baseEnd_523287] using wordTrace_append hprefix tailTrace_523287
  have hstable : (prefixWord ++ tailWord_523287).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523287).length < 2 ^ (prefixWord ++ tailWord_523287).sum := by decide
  have hdescent : baseEnd_523287 < baseStart_523287 := by decide
  rcases family_descends (prefixWord ++ tailWord_523287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_523289 : List Nat := [1, 2, 1, 2, 1, 1, 5, 6]
def baseStart_523289 : Nat := 118140960795 + 523289 * 2 ^ 59
def prefixEnd_523289 : Nat := 4983230072969 + 3 ^ 40 * 523289 * 2
def baseEnd_523289 : Nat := 159228905606345696640559

theorem tailTrace_523289 : CollatzResearch.WordTrace tailWord_523289 prefixEnd_523289 159228905606345696640559 := by
  unfold tailWord_523289
  simp only [CollatzResearch.WordTrace]
  refine ⟨19085917801220798491148921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12723945200813865660765947 19085917801220798491148921)
  ·
    refine ⟨14314438350915598868361691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19085917801220798491148921 14314438350915598868361691)
    ·
      refine ⟨21471657526373398302542537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14314438350915598868361691 21471657526373398302542537)
      ·
        refine ⟨16103743144780048726906903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21471657526373398302542537 16103743144780048726906903)
        ·
          refine ⟨24155614717170073090360355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16103743144780048726906903 24155614717170073090360355)
          ·
            refine ⟨36233422075755109635540533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24155614717170073090360355 36233422075755109635540533)
            ·
              refine ⟨3396883319602041528331925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 36233422075755109635540533 3396883319602041528331925)
              ·
                refine ⟨159228905606345696640559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3396883319602041528331925 159228905606345696640559)
                ·
                  rfl

theorem cell19_523289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 6].length) (baseStart_523289 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_523289 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_523289 prefixEnd_523289 := by exact prefixLift 523289
  have htrace : WordTrace (prefixWord ++ tailWord_523289) baseStart_523289 baseEnd_523289 := by
    simpa [prefixWord, tailWord_523289, baseEnd_523289] using wordTrace_append hprefix tailTrace_523289
  have hstable : (prefixWord ++ tailWord_523289).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523289).length < 2 ^ (prefixWord ++ tailWord_523289).sum := by decide
  have hdescent : baseEnd_523289 < baseStart_523289 := by decide
  rcases family_descends (prefixWord ++ tailWord_523289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_523308 : List Nat := [2, 2, 1, 1, 1, 2, 3, 7]
def baseStart_523308 : Nat := 118140960795 + 523308 * 2 ^ 59
def prefixEnd_523308 : Nat := 4983230072969 + 3 ^ 40 * 523308 * 2
def baseEnd_523308 : Nat := 159234687018159282218285

theorem tailTrace_523308 : CollatzResearch.WordTrace tailWord_523308 prefixEnd_523308 159234687018159282218285 := by
  unfold tailWord_523308
  simp only [CollatzResearch.WordTrace]
  refine ⟨9543305394075982368045289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12724407192101309824060385 9543305394075982368045289)
  ·
    refine ⟨7157479045556986776033967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9543305394075982368045289 7157479045556986776033967)
    ·
      refine ⟨10736218568335480164050951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7157479045556986776033967 10736218568335480164050951)
      ·
        refine ⟨16104327852503220246076427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10736218568335480164050951 16104327852503220246076427)
        ·
          refine ⟨24156491778754830369114641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16104327852503220246076427 24156491778754830369114641)
          ·
            refine ⟨18117368834066122776835981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24156491778754830369114641 18117368834066122776835981)
            ·
              refine ⟨6794013312774796041313493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18117368834066122776835981 6794013312774796041313493)
              ·
                refine ⟨159234687018159282218285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6794013312774796041313493 159234687018159282218285)
                ·
                  rfl

theorem cell19_523308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 7].length) (baseStart_523308 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_523308 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_523308 prefixEnd_523308 := by exact prefixLift 523308
  have htrace : WordTrace (prefixWord ++ tailWord_523308) baseStart_523308 baseEnd_523308 := by
    simpa [prefixWord, tailWord_523308, baseEnd_523308] using wordTrace_append hprefix tailTrace_523308
  have hstable : (prefixWord ++ tailWord_523308).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523308).length < 2 ^ (prefixWord ++ tailWord_523308).sum := by decide
  have hdescent : baseEnd_523308 < baseStart_523308 := by decide
  rcases family_descends (prefixWord ++ tailWord_523308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_523382 : List Nat := [5, 1, 1, 2, 1, 1, 8]
def baseStart_523382 : Nat := 118140960795 + 523382 * 2 ^ 59
def prefixEnd_523382 : Nat := 4983230072969 + 3 ^ 40 * 523382 * 2
def baseEnd_523382 : Nat := 53085734698583012191213

theorem tailTrace_523382 : CollatzResearch.WordTrace tailWord_523382 prefixEnd_523382 53085734698583012191213 := by
  unfold tailWord_523382
  simp only [CollatzResearch.WordTrace]
  refine ⟨1193081861867742210892775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12726206526589250249522933 1193081861867742210892775)
  ·
    refine ⟨1789622792801613316339163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1193081861867742210892775 1789622792801613316339163)
    ·
      refine ⟨2684434189202419974508745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1789622792801613316339163 2684434189202419974508745)
      ·
        refine ⟨2013325641901814980881559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2684434189202419974508745 2013325641901814980881559)
        ·
          refine ⟨3019988462852722471322339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2013325641901814980881559 3019988462852722471322339)
          ·
            refine ⟨4529982694279083706983509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3019988462852722471322339 4529982694279083706983509)
            ·
              refine ⟨53085734698583012191213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4529982694279083706983509 53085734698583012191213)
              ·
                rfl

theorem cell19_523382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 8].length) (baseStart_523382 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_523382 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_523382 prefixEnd_523382 := by exact prefixLift 523382
  have htrace : WordTrace (prefixWord ++ tailWord_523382) baseStart_523382 baseEnd_523382 := by
    simpa [prefixWord, tailWord_523382, baseEnd_523382] using wordTrace_append hprefix tailTrace_523382
  have hstable : (prefixWord ++ tailWord_523382).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523382).length < 2 ^ (prefixWord ++ tailWord_523382).sum := by decide
  have hdescent : baseEnd_523382 < baseStart_523382 := by decide
  rcases family_descends (prefixWord ++ tailWord_523382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_523418 : List Nat := [3, 1, 1, 5, 1, 1, 4, 3]
def baseStart_523418 : Nat := 118140960795 + 523418 * 2 ^ 59
def prefixEnd_523418 : Nat := 4983230072969 + 3 ^ 40 * 523418 * 2
def baseEnd_523418 : Nat := 159268158349711619773541

theorem tailTrace_523418 : CollatzResearch.WordTrace tailWord_523418 prefixEnd_523418 159268158349711619773541 := by
  unfold tailWord_523418
  simp only [CollatzResearch.WordTrace]
  refine ⟨4772655704438363380648727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12727081878502302348396605 4772655704438363380648727)
  ·
    refine ⟨7158983556657545070973091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4772655704438363380648727 7158983556657545070973091)
    ·
      refine ⟨10738475334986317606459637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7158983556657545070973091 10738475334986317606459637)
      ·
        refine ⟨1006732062654967275605591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10738475334986317606459637 1006732062654967275605591)
        ·
          refine ⟨1510098093982450913408387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1006732062654967275605591 1510098093982450913408387)
          ·
            refine ⟨2265147140973676370112581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1510098093982450913408387 2265147140973676370112581)
            ·
              refine ⟨424715088932564319396109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2265147140973676370112581 424715088932564319396109)
              ·
                refine ⟨159268158349711619773541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 424715088932564319396109 159268158349711619773541)
                ·
                  rfl

theorem cell19_523418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 4, 3].length) (baseStart_523418 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_523418 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_523418 prefixEnd_523418 := by exact prefixLift 523418
  have htrace : WordTrace (prefixWord ++ tailWord_523418) baseStart_523418 baseEnd_523418 := by
    simpa [prefixWord, tailWord_523418, baseEnd_523418] using wordTrace_append hprefix tailTrace_523418
  have hstable : (prefixWord ++ tailWord_523418).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523418).length < 2 ^ (prefixWord ++ tailWord_523418).sum := by decide
  have hdescent : baseEnd_523418 < baseStart_523418 := by decide
  rcases family_descends (prefixWord ++ tailWord_523418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_523420 : List Nat := [2, 2, 3, 2, 1, 3, 1, 5]
def baseStart_523420 : Nat := 118140960795 + 523420 * 2 ^ 59
def prefixEnd_523420 : Nat := 4983230072969 + 3 ^ 40 * 523420 * 2
def baseEnd_523420 : Nat := 159268766919376207729091

theorem tailTrace_523420 : CollatzResearch.WordTrace tailWord_523420 prefixEnd_523420 159268766919376207729091 := by
  unfold tailWord_523420
  simp only [CollatzResearch.WordTrace]
  refine ⟨9545347881873103932083857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12727130509164138576111809 9545347881873103932083857)
  ·
    refine ⟨7159010911404827949062893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9545347881873103932083857 7159010911404827949062893)
    ·
      refine ⟨2684629091776810480898585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7159010911404827949062893 2684629091776810480898585)
      ·
        refine ⟨2013471818832607860673939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2684629091776810480898585 2013471818832607860673939)
        ·
          refine ⟨3020207728248911791010909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2013471818832607860673939 3020207728248911791010909)
          ·
            refine ⟨1132577898093341921629091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3020207728248911791010909 1132577898093341921629091)
            ·
              refine ⟨1698866847140012882443637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1132577898093341921629091 1698866847140012882443637)
              ·
                refine ⟨159268766919376207729091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1698866847140012882443637 159268766919376207729091)
                ·
                  rfl

theorem cell19_523420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 1, 5].length) (baseStart_523420 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_523420 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_523420 prefixEnd_523420 := by exact prefixLift 523420
  have htrace : WordTrace (prefixWord ++ tailWord_523420) baseStart_523420 baseEnd_523420 := by
    simpa [prefixWord, tailWord_523420, baseEnd_523420] using wordTrace_append hprefix tailTrace_523420
  have hstable : (prefixWord ++ tailWord_523420).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523420).length < 2 ^ (prefixWord ++ tailWord_523420).sum := by decide
  have hdescent : baseEnd_523420 < baseStart_523420 := by decide
  rcases family_descends (prefixWord ++ tailWord_523420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_523437 : List Nat := [1, 5, 2, 1, 3, 2, 5]
def baseStart_523437 : Nat := 118140960795 + 523437 * 2 ^ 59
def prefixEnd_523437 : Nat := 4983230072969 + 3 ^ 40 * 523437 * 2
def baseEnd_523437 : Nat := 53091313253841735117089

theorem tailTrace_523437 : CollatzResearch.WordTrace tailWord_523437 prefixEnd_523437 53091313253841735117089 := by
  unfold tailWord_523437
  simp only [CollatzResearch.WordTrace]
  refine ⟨19091315804684619767536565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12727543869789746511691043 19091315804684619767536565)
  ·
    refine ⟨1789810856689183103206553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 19091315804684619767536565 1789810856689183103206553)
    ·
      refine ⟨1342358142516887327404915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1789810856689183103206553 1342358142516887327404915)
      ·
        refine ⟨2013537213775330991107373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1342358142516887327404915 2013537213775330991107373)
        ·
          refine ⟨755076455165749121665265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2013537213775330991107373 755076455165749121665265)
          ·
            refine ⟨566307341374311841248949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 755076455165749121665265 566307341374311841248949)
            ·
              refine ⟨53091313253841735117089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 566307341374311841248949 53091313253841735117089)
              ·
                rfl

theorem cell19_523437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 5].length) (baseStart_523437 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_523437 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_523437 prefixEnd_523437 := by exact prefixLift 523437
  have htrace : WordTrace (prefixWord ++ tailWord_523437) baseStart_523437 baseEnd_523437 := by
    simpa [prefixWord, tailWord_523437, baseEnd_523437] using wordTrace_append hprefix tailTrace_523437
  have hstable : (prefixWord ++ tailWord_523437).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523437).length < 2 ^ (prefixWord ++ tailWord_523437).sum := by decide
  have hdescent : baseEnd_523437 < baseStart_523437 := by decide
  rcases family_descends (prefixWord ++ tailWord_523437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_523477 : List Nat := [1, 3, 2, 4, 1, 1, 2, 5]
def baseStart_523477 : Nat := 118140960795 + 523477 * 2 ^ 59
def prefixEnd_523477 : Nat := 4983230072969 + 3 ^ 40 * 523477 * 2
def baseEnd_523477 : Nat := 159286111154816964462269

theorem tailTrace_523477 : CollatzResearch.WordTrace tailWord_523477 prefixEnd_523477 159286111154816964462269 := by
  unfold tailWord_523477
  simp only [CollatzResearch.WordTrace]
  refine ⟨19092774724539706598992685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12728516483026471065995123 19092774724539706598992685)
  ·
    refine ⟨7159790521702389974622257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19092774724539706598992685 7159790521702389974622257)
    ·
      refine ⟨5369842891276792480966693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7159790521702389974622257 5369842891276792480966693)
      ·
        refine ⟨1006845542114398590181255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5369842891276792480966693 1006845542114398590181255)
        ·
          refine ⟨1510268313171597885271883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1006845542114398590181255 1510268313171597885271883)
          ·
            refine ⟨2265402469757396827907825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1510268313171597885271883 2265402469757396827907825)
            ·
              refine ⟨1699051852318047620930869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2265402469757396827907825 1699051852318047620930869)
              ·
                refine ⟨159286111154816964462269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1699051852318047620930869 159286111154816964462269)
                ·
                  rfl

theorem cell19_523477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 2, 5].length) (baseStart_523477 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_523477 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_523477 prefixEnd_523477 := by exact prefixLift 523477
  have htrace : WordTrace (prefixWord ++ tailWord_523477) baseStart_523477 baseEnd_523477 := by
    simpa [prefixWord, tailWord_523477, baseEnd_523477] using wordTrace_append hprefix tailTrace_523477
  have hstable : (prefixWord ++ tailWord_523477).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523477).length < 2 ^ (prefixWord ++ tailWord_523477).sum := by decide
  have hdescent : baseEnd_523477 < baseStart_523477 := by decide
  rcases family_descends (prefixWord ++ tailWord_523477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_523479 : List Nat := [1, 1, 3, 2, 1, 2, 4, 5]
def baseStart_523479 : Nat := 118140960795 + 523479 * 2 ^ 59
def prefixEnd_523479 : Nat := 4983230072969 + 3 ^ 40 * 523479 * 2
def baseEnd_523479 : Nat := 159286719724481552417819

theorem tailTrace_523479 : CollatzResearch.WordTrace tailWord_523479 prefixEnd_523479 159286719724481552417819 := by
  unfold tailWord_523479
  simp only [CollatzResearch.WordTrace]
  refine ⟨19092847670532460940565491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12728565113688307293710327 19092847670532460940565491)
  ·
    refine ⟨28639271505798691410848237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19092847670532460940565491 28639271505798691410848237)
    ·
      refine ⟨10739726814674509279068089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28639271505798691410848237 10739726814674509279068089)
      ·
        refine ⟨8054795111005881959301067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10739726814674509279068089 8054795111005881959301067)
        ·
          refine ⟨12082192666508822938951601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8054795111005881959301067 12082192666508822938951601)
          ·
            refine ⟨9061644499881617204213701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12082192666508822938951601 9061644499881617204213701)
            ·
              refine ⟨1699058343727803225790069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9061644499881617204213701 1699058343727803225790069)
              ·
                refine ⟨159286719724481552417819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1699058343727803225790069 159286719724481552417819)
                ·
                  rfl

theorem cell19_523479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 4, 5].length) (baseStart_523479 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_523479 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_523479 prefixEnd_523479 := by exact prefixLift 523479
  have htrace : WordTrace (prefixWord ++ tailWord_523479) baseStart_523479 baseEnd_523479 := by
    simpa [prefixWord, tailWord_523479, baseEnd_523479] using wordTrace_append hprefix tailTrace_523479
  have hstable : (prefixWord ++ tailWord_523479).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523479).length < 2 ^ (prefixWord ++ tailWord_523479).sum := by decide
  have hdescent : baseEnd_523479 < baseStart_523479 := by decide
  rcases family_descends (prefixWord ++ tailWord_523479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_523498 : List Nat := [3, 1, 3, 1, 1, 10]
def baseStart_523498 : Nat := 118140960795 + 523498 * 2 ^ 59
def prefixEnd_523498 : Nat := 4983230072969 + 3 ^ 40 * 523498 * 2
def baseEnd_523498 : Nat := 17699166792921681999505

theorem tailTrace_523498 : CollatzResearch.WordTrace tailWord_523498 prefixEnd_523498 17699166792921681999505 := by
  unfold tailWord_523498
  simp only [CollatzResearch.WordTrace]
  refine ⟨4773385164365906796376787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12729027104975751457004765 4773385164365906796376787)
  ·
    refine ⟨7160077746548860194565181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4773385164365906796376787 7160077746548860194565181)
    ·
      refine ⟨2685029154955822572961943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7160077746548860194565181 2685029154955822572961943)
      ·
        refine ⟨4027543732433733859442915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2685029154955822572961943 4027543732433733859442915)
        ·
          refine ⟨6041315598650600789164373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4027543732433733859442915 6041315598650600789164373)
          ·
            refine ⟨17699166792921681999505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 6041315598650600789164373 17699166792921681999505)
            ·
              rfl

theorem cell19_523498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 10].length) (baseStart_523498 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_523498 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_523498 prefixEnd_523498 := by exact prefixLift 523498
  have htrace : WordTrace (prefixWord ++ tailWord_523498) baseStart_523498 baseEnd_523498 := by
    simpa [prefixWord, tailWord_523498, baseEnd_523498] using wordTrace_append hprefix tailTrace_523498
  have hstable : (prefixWord ++ tailWord_523498).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523498).length < 2 ^ (prefixWord ++ tailWord_523498).sum := by decide
  have hdescent : baseEnd_523498 < baseStart_523498 := by decide
  rcases family_descends (prefixWord ++ tailWord_523498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_523555 : List Nat := [1, 1, 1, 4, 2, 4, 6]
def baseStart_523555 : Nat := 118140960795 + 523555 * 2 ^ 59
def prefixEnd_523555 : Nat := 4983230072969 + 3 ^ 40 * 523555 * 2
def baseEnd_523555 : Nat := 53103281790578631576241

theorem tailTrace_523555 : CollatzResearch.WordTrace tailWord_523555 prefixEnd_523555 53103281790578631576241 := by
  unfold tailWord_523555
  simp only [CollatzResearch.WordTrace]
  refine ⟨19095619618257125920332119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12730413078838083946888079 19095619618257125920332119)
  ·
    refine ⟨28643429427385688880498179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19095619618257125920332119 28643429427385688880498179)
    ·
      refine ⟨42965144141078533320747269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28643429427385688880498179 42965144141078533320747269)
      ·
        refine ⟨8055964526452224997640113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42965144141078533320747269 8055964526452224997640113)
        ·
          refine ⟨6041973394839168748230085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8055964526452224997640113 6041973394839168748230085)
          ·
            refine ⟨1132870011532344140293141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6041973394839168748230085 1132870011532344140293141)
            ·
              refine ⟨53103281790578631576241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1132870011532344140293141 53103281790578631576241)
              ·
                rfl

theorem cell19_523555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 6].length) (baseStart_523555 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_523555 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_523555 prefixEnd_523555 := by exact prefixLift 523555
  have htrace : WordTrace (prefixWord ++ tailWord_523555) baseStart_523555 baseEnd_523555 := by
    simpa [prefixWord, tailWord_523555, baseEnd_523555] using wordTrace_append hprefix tailTrace_523555
  have hstable : (prefixWord ++ tailWord_523555).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523555).length < 2 ^ (prefixWord ++ tailWord_523555).sum := by decide
  have hdescent : baseEnd_523555 < baseStart_523555 := by decide
  rcases family_descends (prefixWord ++ tailWord_523555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_523572 : List Nat := [2, 5, 1, 1, 1, 1, 2, 6]
def baseStart_523572 : Nat := 118140960795 + 523572 * 2 ^ 59
def prefixEnd_523572 : Nat := 4983230072969 + 3 ^ 40 * 523572 * 2
def baseEnd_523572 : Nat := 159315018213884892350899

theorem tailTrace_523572 : CollatzResearch.WordTrace tailWord_523572 prefixEnd_523572 159315018213884892350899 := by
  unfold tailWord_523572
  simp only [CollatzResearch.WordTrace]
  refine ⟨9548119829597768911850485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12730826439463691882467313 9548119829597768911850485)
  ·
    refine ⟨895136234024790835485983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9548119829597768911850485 895136234024790835485983)
    ·
      refine ⟨1342704351037186253228975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 895136234024790835485983 1342704351037186253228975)
      ·
        refine ⟨2014056526555779379843463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1342704351037186253228975 2014056526555779379843463)
        ·
          refine ⟨3021084789833669069765195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2014056526555779379843463 3021084789833669069765195)
          ·
            refine ⟨4531627184750503604647793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3021084789833669069765195 4531627184750503604647793)
            ·
              refine ⟨3398720388562877703485845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4531627184750503604647793 3398720388562877703485845)
              ·
                refine ⟨159315018213884892350899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3398720388562877703485845 159315018213884892350899)
                ·
                  rfl

theorem cell19_523572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 6].length) (baseStart_523572 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_523572 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_523572 prefixEnd_523572 := by exact prefixLift 523572
  have htrace : WordTrace (prefixWord ++ tailWord_523572) baseStart_523572 baseEnd_523572 := by
    simpa [prefixWord, tailWord_523572, baseEnd_523572] using wordTrace_append hprefix tailTrace_523572
  have hstable : (prefixWord ++ tailWord_523572).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523572).length < 2 ^ (prefixWord ++ tailWord_523572).sum := by decide
  have hdescent : baseEnd_523572 < baseStart_523572 := by decide
  rcases family_descends (prefixWord ++ tailWord_523572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_523591 : List Nat := [1, 1, 4, 1, 2, 3, 4, 3]
def baseStart_523591 : Nat := 118140960795 + 523591 * 2 ^ 59
def prefixEnd_523591 : Nat := 4983230072969 + 3 ^ 40 * 523591 * 2
def baseEnd_523591 : Nat := 159320799625698477928625

theorem tailTrace_523591 : CollatzResearch.WordTrace tailWord_523591 prefixEnd_523591 159320799625698477928625 := by
  unfold tailWord_523591
  simp only [CollatzResearch.WordTrace]
  refine ⟨19096932646126704068642627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12731288430751136045761751 19096932646126704068642627)
  ·
    refine ⟨28645398969190056102963941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19096932646126704068642627 28645398969190056102963941)
    ·
      refine ⟨5371012306723135519305739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28645398969190056102963941 5371012306723135519305739)
      ·
        refine ⟨8056518460084703278958609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5371012306723135519305739 8056518460084703278958609)
        ·
          refine ⟨6042388845063527459218957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8056518460084703278958609 6042388845063527459218957)
          ·
            refine ⟨2265895816898822797207109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6042388845063527459218957 2265895816898822797207109)
            ·
              refine ⟨424855465668529274476333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2265895816898822797207109 424855465668529274476333)
              ·
                refine ⟨159320799625698477928625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 424855465668529274476333 159320799625698477928625)
                ·
                  rfl

theorem cell19_523591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 4, 3].length) (baseStart_523591 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_523591 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_523591 prefixEnd_523591 := by exact prefixLift 523591
  have htrace : WordTrace (prefixWord ++ tailWord_523591) baseStart_523591 baseEnd_523591 := by
    simpa [prefixWord, tailWord_523591, baseEnd_523591] using wordTrace_append hprefix tailTrace_523591
  have hstable : (prefixWord ++ tailWord_523591).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523591).length < 2 ^ (prefixWord ++ tailWord_523591).sum := by decide
  have hdescent : baseEnd_523591 < baseStart_523591 := by decide
  rcases family_descends (prefixWord ++ tailWord_523591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_523629 : List Nat := [1, 5, 1, 1, 1, 4, 2, 4]
def baseStart_523629 : Nat := 118140960795 + 523629 * 2 ^ 59
def prefixEnd_523629 : Nat := 4983230072969 + 3 ^ 40 * 523629 * 2
def baseEnd_523629 : Nat := 159332362449325649084077

theorem tailTrace_523629 : CollatzResearch.WordTrace tailWord_523629 prefixEnd_523629 159332362449325649084077 := by
  unfold tailWord_523629
  simp only [CollatzResearch.WordTrace]
  refine ⟨19098318619989036558525941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12732212413326024372350627 19098318619989036558525941)
  ·
    refine ⟨1790467370623972177361807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 19098318619989036558525941 1790467370623972177361807)
    ·
      refine ⟨2685701055935958266042711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1790467370623972177361807 2685701055935958266042711)
      ·
        refine ⟨4028551583903937399064067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2685701055935958266042711 4028551583903937399064067)
        ·
          refine ⟨6042827375855906098596101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4028551583903937399064067 6042827375855906098596101)
          ·
            refine ⟨1133030132972982393486769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6042827375855906098596101 1133030132972982393486769)
            ·
              refine ⟨849772599729736795115077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1133030132972982393486769 849772599729736795115077)
              ·
                refine ⟨159332362449325649084077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 849772599729736795115077 159332362449325649084077)
                ·
                  rfl

theorem cell19_523629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 2, 4].length) (baseStart_523629 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_523629 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_523629 prefixEnd_523629 := by exact prefixLift 523629
  have htrace : WordTrace (prefixWord ++ tailWord_523629) baseStart_523629 baseEnd_523629 := by
    simpa [prefixWord, tailWord_523629, baseEnd_523629] using wordTrace_append hprefix tailTrace_523629
  have hstable : (prefixWord ++ tailWord_523629).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523629).length < 2 ^ (prefixWord ++ tailWord_523629).sum := by decide
  have hdescent : baseEnd_523629 < baseStart_523629 := by decide
  rcases family_descends (prefixWord ++ tailWord_523629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_523631 : List Nat := [1, 1, 2, 1, 3, 1, 6, 4]
def baseStart_523631 : Nat := 118140960795 + 523631 * 2 ^ 59
def prefixEnd_523631 : Nat := 4983230072969 + 3 ^ 40 * 523631 * 2
def baseEnd_523631 : Nat := 159332971018990237039627

theorem tailTrace_523631 : CollatzResearch.WordTrace tailWord_523631 prefixEnd_523631 159332971018990237039627 := by
  unfold tailWord_523631
  simp only [CollatzResearch.WordTrace]
  refine ⟨19098391565981790900098747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12732261043987860600065831 19098391565981790900098747)
  ·
    refine ⟨28647587348972686350148121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19098391565981790900098747 28647587348972686350148121)
    ·
      refine ⟨21485690511729514762611091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28647587348972686350148121 21485690511729514762611091)
      ·
        refine ⟨32228535767594272143916637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21485690511729514762611091 32228535767594272143916637)
        ·
          refine ⟨12085700912847852053968739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32228535767594272143916637 12085700912847852053968739)
          ·
            refine ⟨18128551369271778080953109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12085700912847852053968739 18128551369271778080953109)
            ·
              refine ⟨849775845434614597544677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 18128551369271778080953109 849775845434614597544677)
              ·
                refine ⟨159332971018990237039627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 849775845434614597544677 159332971018990237039627)
                ·
                  rfl

theorem cell19_523631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 6, 4].length) (baseStart_523631 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_523631 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_523631 prefixEnd_523631 := by exact prefixLift 523631
  have htrace : WordTrace (prefixWord ++ tailWord_523631) baseStart_523631 baseEnd_523631 := by
    simpa [prefixWord, tailWord_523631, baseEnd_523631] using wordTrace_append hprefix tailTrace_523631
  have hstable : (prefixWord ++ tailWord_523631).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523631).length < 2 ^ (prefixWord ++ tailWord_523631).sum := by decide
  have hdescent : baseEnd_523631 < baseStart_523631 := by decide
  rcases family_descends (prefixWord ++ tailWord_523631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_523762 : List Nat := [3, 2, 1, 4, 1, 2, 1, 5]
def baseStart_523762 : Nat := 118140960795 + 523762 * 2 ^ 59
def prefixEnd_523762 : Nat := 4983230072969 + 3 ^ 40 * 523762 * 2
def baseEnd_523762 : Nat := 159372832332020748128159

theorem tailTrace_523762 : CollatzResearch.WordTrace tailWord_523762 prefixEnd_523762 159372832332020748128159 := by
  unfold tailWord_523762
  simp only [CollatzResearch.WordTrace]
  refine ⟨4775792382126800068279385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12735446352338133515411693 4775792382126800068279385)
  ·
    refine ⟨3581844286595100051209539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4775792382126800068279385 3581844286595100051209539)
    ·
      refine ⟨5372766429892650076814309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3581844286595100051209539 5372766429892650076814309)
      ·
        refine ⟨1007393705604871889402683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5372766429892650076814309 1007393705604871889402683)
        ·
          refine ⟨1511090558407307834104025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1007393705604871889402683 1511090558407307834104025)
          ·
            refine ⟨1133317918805480875578019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1511090558407307834104025 1133317918805480875578019)
            ·
              refine ⟨1699976878208221313367029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1133317918805480875578019 1699976878208221313367029)
              ·
                refine ⟨159372832332020748128159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1699976878208221313367029 159372832332020748128159)
                ·
                  rfl

theorem cell19_523762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 1, 5].length) (baseStart_523762 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_523762 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_523762 prefixEnd_523762 := by exact prefixLift 523762
  have htrace : WordTrace (prefixWord ++ tailWord_523762) baseStart_523762 baseEnd_523762 := by
    simpa [prefixWord, tailWord_523762, baseEnd_523762] using wordTrace_append hprefix tailTrace_523762
  have hstable : (prefixWord ++ tailWord_523762).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523762).length < 2 ^ (prefixWord ++ tailWord_523762).sum := by decide
  have hdescent : baseEnd_523762 < baseStart_523762 := by decide
  rcases family_descends (prefixWord ++ tailWord_523762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_523783 : List Nat := [1, 1, 4, 3, 2, 1, 7]
def baseStart_523783 : Nat := 118140960795 + 523783 * 2 ^ 59
def prefixEnd_523783 : Nat := 4983230072969 + 3 ^ 40 * 523783 * 2
def baseEnd_523783 : Nat := 53126407437832973887145

theorem tailTrace_523783 : CollatzResearch.WordTrace tailWord_523783 prefixEnd_523783 53126407437832973887145 := by
  unfold tailWord_523783
  simp only [CollatzResearch.WordTrace]
  refine ⟨19103935461431120859632003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12735956974287413906421335 19103935461431120859632003)
  ·
    refine ⟨28655903192146681289448005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19103935461431120859632003 28655903192146681289448005)
    ·
      refine ⟨5372981848527502741771501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28655903192146681289448005 5372981848527502741771501)
      ·
        refine ⟨2014868193197813528164313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5372981848527502741771501 2014868193197813528164313)
        ·
          refine ⟨1511151144898360146123235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2014868193197813528164313 1511151144898360146123235)
          ·
            refine ⟨2266726717347540219184853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1511151144898360146123235 2266726717347540219184853)
            ·
              refine ⟨53126407437832973887145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2266726717347540219184853 53126407437832973887145)
              ·
                rfl

theorem cell19_523783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 7].length) (baseStart_523783 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_523783 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_523783 prefixEnd_523783 := by exact prefixLift 523783
  have htrace : WordTrace (prefixWord ++ tailWord_523783) baseStart_523783 baseEnd_523783 := by
    simpa [prefixWord, tailWord_523783, baseEnd_523783] using wordTrace_append hprefix tailTrace_523783
  have hstable : (prefixWord ++ tailWord_523783).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523783).length < 2 ^ (prefixWord ++ tailWord_523783).sum := by decide
  have hdescent : baseEnd_523783 < baseStart_523783 := by decide
  rcases family_descends (prefixWord ++ tailWord_523783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_523800 : List Nat := [2, 1, 2, 3, 4, 1, 2, 4]
def baseStart_523800 : Nat := 118140960795 + 523800 * 2 ^ 59
def prefixEnd_523800 : Nat := 4983230072969 + 3 ^ 40 * 523800 * 2
def baseEnd_523800 : Nat := 159384395155647919283611

theorem tailTrace_523800 : CollatzResearch.WordTrace tailWord_523800 prefixEnd_523800 159384395155647919283611 := by
  unfold tailWord_523800
  simp only [CollatzResearch.WordTrace]
  refine ⟨9552277751184766381500427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12736370334913021842000569 9552277751184766381500427)
  ·
    refine ⟨14328416626777149572250641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9552277751184766381500427 14328416626777149572250641)
    ·
      refine ⟨10746312470082862179187981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14328416626777149572250641 10746312470082862179187981)
      ·
        refine ⟨4029867176281073317195493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10746312470082862179187981 4029867176281073317195493)
        ·
          refine ⟨755600095552701246974155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4029867176281073317195493 755600095552701246974155)
          ·
            refine ⟨1133400143329051870461233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 755600095552701246974155 1133400143329051870461233)
            ·
              refine ⟨850050107496788902845925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1133400143329051870461233 850050107496788902845925)
              ·
                refine ⟨159384395155647919283611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 850050107496788902845925 159384395155647919283611)
                ·
                  rfl

theorem cell19_523800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 2, 4].length) (baseStart_523800 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_523800 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_523800 prefixEnd_523800 := by exact prefixLift 523800
  have htrace : WordTrace (prefixWord ++ tailWord_523800) baseStart_523800 baseEnd_523800 := by
    simpa [prefixWord, tailWord_523800, baseEnd_523800] using wordTrace_append hprefix tailTrace_523800
  have hstable : (prefixWord ++ tailWord_523800).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523800).length < 2 ^ (prefixWord ++ tailWord_523800).sum := by decide
  have hdescent : baseEnd_523800 < baseStart_523800 := by decide
  rcases family_descends (prefixWord ++ tailWord_523800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_523853 : List Nat := [1, 6, 1, 1, 4, 1, 1, 4]
def baseStart_523853 : Nat := 118140960795 + 523853 * 2 ^ 59
def prefixEnd_523853 : Nat := 4983230072969 + 3 ^ 40 * 523853 * 2
def baseEnd_523853 : Nat := 159400522251759500105689

theorem tailTrace_523853 : CollatzResearch.WordTrace tailWord_523853 prefixEnd_523853 159400522251759500105689 := by
  unfold tailWord_523853
  simp only [CollatzResearch.WordTrace]
  refine ⟨19106488571177522814680213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12737659047451681876453475 19106488571177522814680213)
  ·
    refine ⟨895616651773946381938135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 19106488571177522814680213 895616651773946381938135)
    ·
      refine ⟨1343424977660919572907203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 895616651773946381938135 1343424977660919572907203)
      ·
        refine ⟨2015137466491379359360805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1343424977660919572907203 2015137466491379359360805)
        ·
          refine ⟨377838274967133629880151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2015137466491379359360805 377838274967133629880151)
          ·
            refine ⟨566757412450700444820227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 377838274967133629880151 566757412450700444820227)
            ·
              refine ⟨850136118676050667230341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 566757412450700444820227 850136118676050667230341)
              ·
                refine ⟨159400522251759500105689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 850136118676050667230341 159400522251759500105689)
                ·
                  rfl

theorem cell19_523853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 1, 4].length) (baseStart_523853 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_523853 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_523853 prefixEnd_523853 := by exact prefixLift 523853
  have htrace : WordTrace (prefixWord ++ tailWord_523853) baseStart_523853 baseEnd_523853 := by
    simpa [prefixWord, tailWord_523853, baseEnd_523853] using wordTrace_append hprefix tailTrace_523853
  have hstable : (prefixWord ++ tailWord_523853).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523853).length < 2 ^ (prefixWord ++ tailWord_523853).sum := by decide
  have hdescent : baseEnd_523853 < baseStart_523853 := by decide
  rcases family_descends (prefixWord ++ tailWord_523853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_523876 : List Nat := [2, 3, 1, 1, 2, 4, 3, 3]
def baseStart_523876 : Nat := 118140960795 + 523876 * 2 ^ 59
def prefixEnd_523876 : Nat := 4983230072969 + 3 ^ 40 * 523876 * 2
def baseEnd_523876 : Nat := 159407520802902261594515

theorem tailTrace_523876 : CollatzResearch.WordTrace tailWord_523876 prefixEnd_523876 159407520802902261594515 := by
  unfold tailWord_523876
  simp only [CollatzResearch.WordTrace]
  refine ⟨9553663725047098871383741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12738218300062798495178321 9553663725047098871383741)
  ·
    refine ⟨3582623896892662076768903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9553663725047098871383741 3582623896892662076768903)
    ·
      refine ⟨5373935845338993115153355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3582623896892662076768903 5373935845338993115153355)
      ·
        refine ⟨8060903768008489672730033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5373935845338993115153355 8060903768008489672730033)
        ·
          refine ⟨6045677826006367254547525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8060903768008489672730033 6045677826006367254547525)
          ·
            refine ⟨1133564592376193860227661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6045677826006367254547525 1133564592376193860227661)
            ·
              refine ⟨425086722141072697585373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1133564592376193860227661 425086722141072697585373)
              ·
                refine ⟨159407520802902261594515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 425086722141072697585373 159407520802902261594515)
                ·
                  rfl

theorem cell19_523876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 3, 3].length) (baseStart_523876 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_523876 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_523876 prefixEnd_523876 := by exact prefixLift 523876
  have htrace : WordTrace (prefixWord ++ tailWord_523876) baseStart_523876 baseEnd_523876 := by
    simpa [prefixWord, tailWord_523876, baseEnd_523876] using wordTrace_append hprefix tailTrace_523876
  have hstable : (prefixWord ++ tailWord_523876).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523876).length < 2 ^ (prefixWord ++ tailWord_523876).sum := by decide
  have hdescent : baseEnd_523876 < baseStart_523876 := by decide
  rcases family_descends (prefixWord ++ tailWord_523876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_523899 : List Nat := [1, 1, 1, 1, 1, 4, 10]
def baseStart_523899 : Nat := 118140960795 + 523899 * 2 ^ 59
def prefixEnd_523899 : Nat := 4983230072969 + 3 ^ 40 * 523899 * 2
def baseEnd_523899 : Nat := 53138173118015007694447

theorem tailTrace_523899 : CollatzResearch.WordTrace tailWord_523899 prefixEnd_523899 53138173118015007694447 := by
  unfold tailWord_523899
  simp only [CollatzResearch.WordTrace]
  refine ⟨19108166329010872670854751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12738777552673915113903167 19108166329010872670854751)
  ·
    refine ⟨28662249493516309006282127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19108166329010872670854751 28662249493516309006282127)
    ·
      refine ⟨42993374240274463509423191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28662249493516309006282127 42993374240274463509423191)
      ·
        refine ⟨64490061360411695264134787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42993374240274463509423191 64490061360411695264134787)
        ·
          refine ⟨96735092040617542896202181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64490061360411695264134787 96735092040617542896202181)
          ·
            refine ⟨18137829757615789293037909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 96735092040617542896202181 18137829757615789293037909)
            ·
              refine ⟨53138173118015007694447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 18137829757615789293037909 53138173118015007694447)
              ·
                rfl

theorem cell19_523899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 10].length) (baseStart_523899 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_523899 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_523899 prefixEnd_523899 := by exact prefixLift 523899
  have htrace : WordTrace (prefixWord ++ tailWord_523899) baseStart_523899 baseEnd_523899 := by
    simpa [prefixWord, tailWord_523899, baseEnd_523899] using wordTrace_append hprefix tailTrace_523899
  have hstable : (prefixWord ++ tailWord_523899).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523899).length < 2 ^ (prefixWord ++ tailWord_523899).sum := by decide
  have hdescent : baseEnd_523899 < baseStart_523899 := by decide
  rcases family_descends (prefixWord ++ tailWord_523899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_523950 : List Nat := [4, 1, 4, 1, 2, 2, 5]
def baseStart_523950 : Nat := 118140960795 + 523950 * 2 ^ 59
def prefixEnd_523950 : Nat := 4983230072969 + 3 ^ 40 * 523950 * 2
def baseEnd_523950 : Nat := 53143345960164005316623

theorem tailTrace_523950 : CollatzResearch.WordTrace tailWord_523950 prefixEnd_523950 53143345960164005316623 := by
  unfold tailWord_523950
  simp only [CollatzResearch.WordTrace]
  refine ⟨2388753306478263547620163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12740017634550738920640869 2388753306478263547620163)
  ·
    refine ⟨3583129959717395321430245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2388753306478263547620163 3583129959717395321430245)
    ·
      refine ⟨671836867447011622768171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3583129959717395321430245 671836867447011622768171)
      ·
        refine ⟨1007755301170517434152257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 671836867447011622768171 1007755301170517434152257)
        ·
          refine ⟨755816475877888075614193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1007755301170517434152257 755816475877888075614193)
          ·
            refine ⟨566862356908416056710645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 755816475877888075614193 566862356908416056710645)
            ·
              refine ⟨53143345960164005316623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 566862356908416056710645 53143345960164005316623)
              ·
                rfl

theorem cell19_523950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 5].length) (baseStart_523950 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_523950 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_523950 prefixEnd_523950 := by exact prefixLift 523950
  have htrace : WordTrace (prefixWord ++ tailWord_523950) baseStart_523950 baseEnd_523950 := by
    simpa [prefixWord, tailWord_523950, baseEnd_523950] using wordTrace_append hprefix tailTrace_523950
  have hstable : (prefixWord ++ tailWord_523950).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523950).length < 2 ^ (prefixWord ++ tailWord_523950).sum := by decide
  have hdescent : baseEnd_523950 < baseStart_523950 := by decide
  rcases family_descends (prefixWord ++ tailWord_523950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524068 : List Nat := [2, 3, 1, 3, 2, 2, 6]
def baseStart_524068 : Nat := 118140960795 + 524068 * 2 ^ 59
def prefixEnd_524068 : Nat := 4983230072969 + 3 ^ 40 * 524068 * 2
def baseEnd_524068 : Nat := 53155314496900901775775

theorem tailTrace_524068 : CollatzResearch.WordTrace tailWord_524068 prefixEnd_524068 53155314496900901775775 := by
  unfold tailWord_524068
  simp only [CollatzResearch.WordTrace]
  refine ⟨9557165132699307266878429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12742886843599076355837905 9557165132699307266878429)
  ·
    refine ⟨3583936924762240225079411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9557165132699307266878429 3583936924762240225079411)
    ·
      refine ⟨5375905387143360337619117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3583936924762240225079411 5375905387143360337619117)
      ·
        refine ⟨2015964520178760126607169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5375905387143360337619117 2015964520178760126607169)
        ·
          refine ⟨1511973390134070094955377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2015964520178760126607169 1511973390134070094955377)
          ·
            refine ⟨1133980042600552571216533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1511973390134070094955377 1133980042600552571216533)
            ·
              refine ⟨53155314496900901775775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1133980042600552571216533 53155314496900901775775)
              ·
                rfl

theorem cell19_524068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 6].length) (baseStart_524068 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_524068 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_524068 prefixEnd_524068 := by exact prefixLift 524068
  have htrace : WordTrace (prefixWord ++ tailWord_524068) baseStart_524068 baseEnd_524068 := by
    simpa [prefixWord, tailWord_524068, baseEnd_524068] using wordTrace_append hprefix tailTrace_524068
  have hstable : (prefixWord ++ tailWord_524068).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524068).length < 2 ^ (prefixWord ++ tailWord_524068).sum := by decide
  have hdescent : baseEnd_524068 < baseStart_524068 := by decide
  rcases family_descends (prefixWord ++ tailWord_524068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524102 : List Nat := [6, 1, 1, 2, 1, 2, 1, 5]
def baseStart_524102 : Nat := 118140960795 + 524102 * 2 ^ 59
def prefixEnd_524102 : Nat := 4983230072969 + 3 ^ 40 * 524102 * 2
def baseEnd_524102 : Nat := 159476289175000700571677

theorem tailTrace_524102 : CollatzResearch.WordTrace tailWord_524102 prefixEnd_524102 159476289175000700571677 := by
  unfold tailWord_524102
  simp only [CollatzResearch.WordTrace]
  refine ⟨597361573352357448140455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 12743713564850292226996373 597361573352357448140455)
  ·
    refine ⟨896042360028536172210683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 597361573352357448140455 896042360028536172210683)
    ·
      refine ⟨1344063540042804258316025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 896042360028536172210683 1344063540042804258316025)
      ·
        refine ⟨1008047655032103193737019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1344063540042804258316025 1008047655032103193737019)
        ·
          refine ⟨1512071482548154790605529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1008047655032103193737019 1512071482548154790605529)
          ·
            refine ⟨1134053611911116092954147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1512071482548154790605529 1134053611911116092954147)
            ·
              refine ⟨1701080417866674139431221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1134053611911116092954147 1701080417866674139431221)
              ·
                refine ⟨159476289175000700571677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1701080417866674139431221 159476289175000700571677)
                ·
                  rfl

theorem cell19_524102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 1, 5].length) (baseStart_524102 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_524102 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_524102 prefixEnd_524102 := by exact prefixLift 524102
  have htrace : WordTrace (prefixWord ++ tailWord_524102) baseStart_524102 baseEnd_524102 := by
    simpa [prefixWord, tailWord_524102, baseEnd_524102] using wordTrace_append hprefix tailTrace_524102
  have hstable : (prefixWord ++ tailWord_524102).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524102).length < 2 ^ (prefixWord ++ tailWord_524102).sum := by decide
  have hdescent : baseEnd_524102 < baseStart_524102 := by decide
  rcases family_descends (prefixWord ++ tailWord_524102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524104 : List Nat := [2, 1, 3, 1, 1, 6, 2, 3]
def baseStart_524104 : Nat := 118140960795 + 524104 * 2 ^ 59
def prefixEnd_524104 : Nat := 4983230072969 + 3 ^ 40 * 524104 * 2
def baseEnd_524104 : Nat := 159476897744665288527227

theorem tailTrace_524104 : CollatzResearch.WordTrace tailWord_524104 prefixEnd_524104 159476897744665288527227 := by
  unfold tailWord_524104
  simp only [CollatzResearch.WordTrace]
  refine ⟨9557821646634096341033683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12743762195512128454711577 9557821646634096341033683)
  ·
    refine ⟨14336732469951144511550525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9557821646634096341033683 14336732469951144511550525)
    ·
      refine ⟨5376274676231679191831447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14336732469951144511550525 5376274676231679191831447)
      ·
        refine ⟨8064412014347518787747171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5376274676231679191831447 8064412014347518787747171)
        ·
          refine ⟨12096618021521278181620757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8064412014347518787747171 12096618021521278181620757)
          ·
            refine ⟨567028969758809914763473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 12096618021521278181620757 567028969758809914763473)
            ·
              refine ⟨425271727319107436072605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 567028969758809914763473 425271727319107436072605)
              ·
                refine ⟨159476897744665288527227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 425271727319107436072605 159476897744665288527227)
                ·
                  rfl

theorem cell19_524104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 2, 3].length) (baseStart_524104 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_524104 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_524104 prefixEnd_524104 := by exact prefixLift 524104
  have htrace : WordTrace (prefixWord ++ tailWord_524104) baseStart_524104 baseEnd_524104 := by
    simpa [prefixWord, tailWord_524104, baseEnd_524104] using wordTrace_append hprefix tailTrace_524104
  have hstable : (prefixWord ++ tailWord_524104).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524104).length < 2 ^ (prefixWord ++ tailWord_524104).sum := by decide
  have hdescent : baseEnd_524104 < baseStart_524104 := by decide
  rcases family_descends (prefixWord ++ tailWord_524104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524127 : List Nat := [1, 1, 2, 3, 1, 4, 7]
def baseStart_524127 : Nat := 118140960795 + 524127 * 2 ^ 59
def prefixEnd_524127 : Nat := 4983230072969 + 3 ^ 40 * 524127 * 2
def baseEnd_524127 : Nat := 53161298765269350005351

theorem tailTrace_524127 : CollatzResearch.WordTrace tailWord_524127 prefixEnd_524127 53161298765269350005351 := by
  unfold tailWord_524127
  simp only [CollatzResearch.WordTrace]
  refine ⟨19116482172184867610154635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12744321448123245073436423 19116482172184867610154635)
  ·
    refine ⟨28674723258277301415231953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19116482172184867610154635 28674723258277301415231953)
    ·
      refine ⟨21506042443707976061423965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28674723258277301415231953 21506042443707976061423965)
      ·
        refine ⟨8064765916390491023033987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21506042443707976061423965 8064765916390491023033987)
        ·
          refine ⟨12097148874585736534550981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8064765916390491023033987 12097148874585736534550981)
          ·
            refine ⟨2268215413984825600228309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12097148874585736534550981 2268215413984825600228309)
            ·
              refine ⟨53161298765269350005351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2268215413984825600228309 53161298765269350005351)
              ·
                rfl

theorem cell19_524127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 7].length) (baseStart_524127 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_524127 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_524127 prefixEnd_524127 := by exact prefixLift 524127
  have htrace : WordTrace (prefixWord ++ tailWord_524127) baseStart_524127 baseEnd_524127 := by
    simpa [prefixWord, tailWord_524127, baseEnd_524127] using wordTrace_append hprefix tailTrace_524127
  have hstable : (prefixWord ++ tailWord_524127).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524127).length < 2 ^ (prefixWord ++ tailWord_524127).sum := by decide
  have hdescent : baseEnd_524127 < baseStart_524127 := by decide
  rcases family_descends (prefixWord ++ tailWord_524127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524142 : List Nat := [4, 1, 2, 3, 1, 2, 2, 4]
def baseStart_524142 : Nat := 118140960795 + 524142 * 2 ^ 59
def prefixEnd_524142 : Nat := 4983230072969 + 3 ^ 40 * 524142 * 2
def baseEnd_524142 : Nat := 159488460568292459682679

theorem tailTrace_524142 : CollatzResearch.WordTrace tailWord_524142 prefixEnd_524142 159488460568292459682679 := by
  unfold tailWord_524142
  simp only [CollatzResearch.WordTrace]
  refine ⟨2389628658391315646493835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12744686178087016781300453 2389628658391315646493835)
  ·
    refine ⟨3584442987586973469740753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2389628658391315646493835 3584442987586973469740753)
    ·
      refine ⟨2688332240690230102305565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3584442987586973469740753 2688332240690230102305565)
      ·
        refine ⟨1008124590258836288364587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2688332240690230102305565 1008124590258836288364587)
        ·
          refine ⟨1512186885388254432546881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1008124590258836288364587 1512186885388254432546881)
          ·
            refine ⟨1134140164041190824410161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1512186885388254432546881 1134140164041190824410161)
            ·
              refine ⟨850605123030893118307621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1134140164041190824410161 850605123030893118307621)
              ·
                refine ⟨159488460568292459682679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 850605123030893118307621 159488460568292459682679)
                ·
                  rfl

theorem cell19_524142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 2, 4].length) (baseStart_524142 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_524142 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_524142 prefixEnd_524142 := by exact prefixLift 524142
  have htrace : WordTrace (prefixWord ++ tailWord_524142) baseStart_524142 baseEnd_524142 := by
    simpa [prefixWord, tailWord_524142, baseEnd_524142] using wordTrace_append hprefix tailTrace_524142
  have hstable : (prefixWord ++ tailWord_524142).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524142).length < 2 ^ (prefixWord ++ tailWord_524142).sum := by decide
  have hdescent : baseEnd_524142 < baseStart_524142 := by decide
  rcases family_descends (prefixWord ++ tailWord_524142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524165 : List Nat := [1, 3, 1, 1, 3, 2, 1, 7]
def baseStart_524165 : Nat := 118140960795 + 524165 * 2 ^ 59
def prefixEnd_524165 : Nat := 4983230072969 + 3 ^ 40 * 524165 * 2
def baseEnd_524165 : Nat := 159495459119435221171505

theorem tailTrace_524165 : CollatzResearch.WordTrace tailWord_524165 prefixEnd_524165 159495459119435221171505 := by
  unfold tailWord_524165
  simp only [CollatzResearch.WordTrace]
  refine ⟨19117868146047200100037949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12745245430698133400025299 19117868146047200100037949)
  ·
    refine ⟨7169200554767700037514231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19117868146047200100037949 7169200554767700037514231)
    ·
      refine ⟨10753800832151550056271347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7169200554767700037514231 10753800832151550056271347)
      ·
        refine ⟨16130701248227325084407021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10753800832151550056271347 16130701248227325084407021)
        ·
          refine ⟨6049012968085246906652633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16130701248227325084407021 6049012968085246906652633)
          ·
            refine ⟨4536759726063935179989475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6049012968085246906652633 4536759726063935179989475)
            ·
              refine ⟨6805139589095902769984213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4536759726063935179989475 6805139589095902769984213)
              ·
                refine ⟨159495459119435221171505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6805139589095902769984213 159495459119435221171505)
                ·
                  rfl

theorem cell19_524165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 7].length) (baseStart_524165 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_524165 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_524165 prefixEnd_524165 := by exact prefixLift 524165
  have htrace : WordTrace (prefixWord ++ tailWord_524165) baseStart_524165 baseEnd_524165 := by
    simpa [prefixWord, tailWord_524165, baseEnd_524165] using wordTrace_append hprefix tailTrace_524165
  have hstable : (prefixWord ++ tailWord_524165).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524165).length < 2 ^ (prefixWord ++ tailWord_524165).sum := by decide
  have hdescent : baseEnd_524165 < baseStart_524165 := by decide
  rcases family_descends (prefixWord ++ tailWord_524165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524199 : List Nat := [1, 1, 6, 1, 2, 3, 1, 4]
def baseStart_524199 : Nat := 118140960795 + 524199 * 2 ^ 59
def prefixEnd_524199 : Nat := 4983230072969 + 3 ^ 40 * 524199 * 2
def baseEnd_524199 : Nat := 159505804803733216415857

theorem tailTrace_524199 : CollatzResearch.WordTrace tailWord_524199 prefixEnd_524199 159505804803733216415857 := by
  unfold tailWord_524199
  simp only [CollatzResearch.WordTrace]
  refine ⟨19119108227924023906775651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12746072151949349271183767 19119108227924023906775651)
  ·
    refine ⟨28678662341886035860163477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19119108227924023906775651 28678662341886035860163477)
    ·
      refine ⟨1344312297275907930945163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 28678662341886035860163477 1344312297275907930945163)
      ·
        refine ⟨2016468445913861896417745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1344312297275907930945163 2016468445913861896417745)
        ·
          refine ⟨1512351334435396422313309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2016468445913861896417745 1512351334435396422313309)
          ·
            refine ⟨567131750413273658367491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1512351334435396422313309 567131750413273658367491)
            ·
              refine ⟨850697625619910487551237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 567131750413273658367491 850697625619910487551237)
              ·
                refine ⟨159505804803733216415857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 850697625619910487551237 159505804803733216415857)
                ·
                  rfl

theorem cell19_524199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 1, 4].length) (baseStart_524199 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_524199 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_524199 prefixEnd_524199 := by exact prefixLift 524199
  have htrace : WordTrace (prefixWord ++ tailWord_524199) baseStart_524199 baseEnd_524199 := by
    simpa [prefixWord, tailWord_524199, baseEnd_524199] using wordTrace_append hprefix tailTrace_524199
  have hstable : (prefixWord ++ tailWord_524199).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524199).length < 2 ^ (prefixWord ++ tailWord_524199).sum := by decide
  have hdescent : baseEnd_524199 < baseStart_524199 := by decide
  rcases family_descends (prefixWord ++ tailWord_524199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524260 : List Nat := [2, 3, 1, 1, 1, 1, 4, 6]
def baseStart_524260 : Nat := 118140960795 + 524260 * 2 ^ 59
def prefixEnd_524260 : Nat := 4983230072969 + 3 ^ 40 * 524260 * 2
def baseEnd_524260 : Nat := 159524366178503149060135

theorem tailTrace_524260 : CollatzResearch.WordTrace tailWord_524260 prefixEnd_524260 159524366178503149060135 := by
  unfold tailWord_524260
  simp only [CollatzResearch.WordTrace]
  refine ⟨9560666540351515662373117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12747555387135354216497489 9560666540351515662373117)
  ·
    refine ⟨3585249952631818373389919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9560666540351515662373117 3585249952631818373389919)
    ·
      refine ⟨5377874928947727560084879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3585249952631818373389919 5377874928947727560084879)
      ·
        refine ⟨8066812393421591340127319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5377874928947727560084879 8066812393421591340127319)
        ·
          refine ⟨12100218590132387010190979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8066812393421591340127319 12100218590132387010190979)
          ·
            refine ⟨18150327885198580515286469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12100218590132387010190979 18150327885198580515286469)
            ·
              refine ⟨3403186478474733846616213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18150327885198580515286469 3403186478474733846616213)
              ·
                refine ⟨159524366178503149060135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3403186478474733846616213 159524366178503149060135)
                ·
                  rfl

theorem cell19_524260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 6].length) (baseStart_524260 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_524260 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_524260 prefixEnd_524260 := by exact prefixLift 524260
  have htrace : WordTrace (prefixWord ++ tailWord_524260) baseStart_524260 baseEnd_524260 := by
    simpa [prefixWord, tailWord_524260, baseEnd_524260] using wordTrace_append hprefix tailTrace_524260
  have hstable : (prefixWord ++ tailWord_524260).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524260).length < 2 ^ (prefixWord ++ tailWord_524260).sum := by decide
  have hdescent : baseEnd_524260 < baseStart_524260 := by decide
  rcases family_descends (prefixWord ++ tailWord_524260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_524273 : List Nat := [1, 2, 2, 2, 6, 1, 2, 3]
def baseStart_524273 : Nat := 118140960795 + 524273 * 2 ^ 59
def prefixEnd_524273 : Nat := 4983230072969 + 3 ^ 40 * 524273 * 2
def baseEnd_524273 : Nat := 159528321881322970771211

theorem tailTrace_524273 : CollatzResearch.WordTrace tailWord_524273 prefixEnd_524273 159528321881322970771211 := by
  unfold tailWord_524273
  simp only [CollatzResearch.WordTrace]
  refine ⟨19121807229655934544969473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12747871486437289696646315 19121807229655934544969473)
  ·
    refine ⟨14341355422241950908727105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19121807229655934544969473 14341355422241950908727105)
    ·
      refine ⟨10756016566681463181545329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14341355422241950908727105 10756016566681463181545329)
      ·
        refine ⟨8067012425011097386158997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10756016566681463181545329 8067012425011097386158997)
        ·
          refine ⟨378141207422395189976203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 8067012425011097386158997 378141207422395189976203)
          ·
            refine ⟨567211811133592784964305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 378141207422395189976203 567211811133592784964305)
            ·
              refine ⟨425408858350194588723229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 567211811133592784964305 425408858350194588723229)
              ·
                refine ⟨159528321881322970771211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 425408858350194588723229 159528321881322970771211)
                ·
                  rfl

theorem cell19_524273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 2, 3].length) (baseStart_524273 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_524273 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_524273 prefixEnd_524273 := by exact prefixLift 524273
  have htrace : WordTrace (prefixWord ++ tailWord_524273) baseStart_524273 baseEnd_524273 := by
    simpa [prefixWord, tailWord_524273, baseEnd_524273] using wordTrace_append hprefix tailTrace_524273
  have hstable : (prefixWord ++ tailWord_524273).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_524273).length < 2 ^ (prefixWord ++ tailWord_524273).sum := by decide
  have hdescent : baseEnd_524273 < baseStart_524273 := by decide
  rcases family_descends (prefixWord ++ tailWord_524273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan19Incremental
