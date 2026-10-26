import V185TrunkScan21Chunk072

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_884575 : List Nat := [1, 1, 2, 3, 1, 4, 4, 2, 3]
def baseStart_884575 : Nat := 118140960795 + 884575 * 2 ^ 59
def prefixEnd_884575 : Nat := 4983230072969 + 3 ^ 40 * 884575 * 2
def baseEnd_884575 : Nat := 201872066644880813308631

theorem tailTrace_884575 : CollatzResearch.WordTrace tailWord_884575 prefixEnd_884575 201872066644880813308631 := by
  unfold tailWord_884575
  simp only [CollatzResearch.WordTrace]
  refine ⟨32263100770343323227543179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21508733846895548818362119 32263100770343323227543179)
  ·
    refine ⟨48394651155514984841314769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32263100770343323227543179 48394651155514984841314769)
    ·
      refine ⟨36295988366636238630986077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48394651155514984841314769 36295988366636238630986077)
      ·
        refine ⟨13610995637488589486619779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36295988366636238630986077 13610995637488589486619779)
        ·
          refine ⟨20416493456232884229929669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13610995637488589486619779 20416493456232884229929669)
          ·
            refine ⟨3828092523043665793111813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20416493456232884229929669 3828092523043665793111813)
            ·
              refine ⟨717767348070687336208465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3828092523043665793111813 717767348070687336208465)
              ·
                refine ⟨538325511053015502156349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 717767348070687336208465 538325511053015502156349)
                ·
                  refine ⟨201872066644880813308631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 538325511053015502156349 201872066644880813308631)
                  ·
                    rfl

theorem cell21_884575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 4, 2, 3].length) (baseStart_884575 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_884575 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_884575 prefixEnd_884575 := by exact prefixLift 884575
  have htrace : WordTrace (prefixWord ++ tailWord_884575) baseStart_884575 baseEnd_884575 := by
    simpa [prefixWord, tailWord_884575, baseEnd_884575] using wordTrace_append hprefix tailTrace_884575
  have hstable : (prefixWord ++ tailWord_884575).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_884575).length < 2 ^ (prefixWord ++ tailWord_884575).sum := by decide
  have hdescent : baseEnd_884575 < baseStart_884575 := by decide
  rcases family_descends (prefixWord ++ tailWord_884575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_884634 : List Nat := [3, 1, 1, 4, 2, 2, 2, 1, 5]
def baseStart_884634 : Nat := 118140960795 + 884634 * 2 ^ 59
def prefixEnd_884634 : Nat := 4983230072969 + 3 ^ 40 * 884634 * 2
def baseEnd_884634 : Nat := 201885531248709821825177

theorem tailTrace_884634 : CollatzResearch.WordTrace tailWord_884634 prefixEnd_884634 201885531248709821825177 := by
  unfold tailWord_884634
  simp only [CollatzResearch.WordTrace]
  refine ⟨8066313169282394075985239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21510168451419717535960637 8066313169282394075985239)
  ·
    refine ⟨12099469753923591113977859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8066313169282394075985239 12099469753923591113977859)
    ·
      refine ⟨18149204630885386670966789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12099469753923591113977859 18149204630885386670966789)
      ·
        refine ⟨3402975868291010000806273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18149204630885386670966789 3402975868291010000806273)
        ·
          refine ⟨2552231901218257500604705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3402975868291010000806273 2552231901218257500604705)
          ·
            refine ⟨1914173925913693125453529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2552231901218257500604705 1914173925913693125453529)
            ·
              refine ⟨1435630444435269844090147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1914173925913693125453529 1435630444435269844090147)
              ·
                refine ⟨2153445666652904766135221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1435630444435269844090147 2153445666652904766135221)
                ·
                  refine ⟨201885531248709821825177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2153445666652904766135221 201885531248709821825177)
                  ·
                    rfl

theorem cell21_884634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 2, 1, 5].length) (baseStart_884634 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_884634 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_884634 prefixEnd_884634 := by exact prefixLift 884634
  have htrace : WordTrace (prefixWord ++ tailWord_884634) baseStart_884634 baseEnd_884634 := by
    simpa [prefixWord, tailWord_884634, baseEnd_884634] using wordTrace_append hprefix tailTrace_884634
  have hstable : (prefixWord ++ tailWord_884634).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_884634).length < 2 ^ (prefixWord ++ tailWord_884634).sum := by decide
  have hdescent : baseEnd_884634 < baseStart_884634 := by decide
  rcases family_descends (prefixWord ++ tailWord_884634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_884738 : List Nat := [3, 4, 1, 13]
def baseStart_884738 : Nat := 118140960795 + 884738 * 2 ^ 59
def prefixEnd_884738 : Nat := 4983230072969 + 3 ^ 40 * 884738 * 2
def baseEnd_884738 : Nat := 830902327019048362517

theorem tailTrace_884738 : CollatzResearch.WordTrace tailWord_884738 prefixEnd_884738 830902327019048362517 := by
  unfold tailWord_884738
  simp only [CollatzResearch.WordTrace]
  refine ⟨8067261467188200516431717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21512697245835201377151245 8067261467188200516431717)
  ·
    refine ⟨1512611525097787596830947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8067261467188200516431717 1512611525097787596830947)
    ·
      refine ⟨2268917287646681395246421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1512611525097787596830947 2268917287646681395246421)
      ·
        refine ⟨830902327019048362517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 13 2268917287646681395246421 830902327019048362517)
        ·
          rfl

theorem cell21_884738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 13].length) (baseStart_884738 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_884738 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_884738 prefixEnd_884738 := by exact prefixLift 884738
  have htrace : WordTrace (prefixWord ++ tailWord_884738) baseStart_884738 baseEnd_884738 := by
    simpa [prefixWord, tailWord_884738, baseEnd_884738] using wordTrace_append hprefix tailTrace_884738
  have hstable : (prefixWord ++ tailWord_884738).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_884738).length < 2 ^ (prefixWord ++ tailWord_884738).sum := by decide
  have hdescent : baseEnd_884738 < baseStart_884738 := by decide
  rcases family_descends (prefixWord ++ tailWord_884738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_884772 : List Nat := [2, 3, 1, 4, 2, 1, 3, 5]
def baseStart_884772 : Nat := 118140960795 + 884772 * 2 ^ 59
def prefixEnd_884772 : Nat := 4983230072969 + 3 ^ 40 * 884772 * 2
def baseEnd_884772 : Nat := 67305674909617416174965

theorem tailTrace_884772 : CollatzResearch.WordTrace tailWord_884772 prefixEnd_884772 67305674909617416174965 := by
  unfold tailWord_884772
  simp only [CollatzResearch.WordTrace]
  refine ⟨16135142975314812936232285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21513523967086417248309713 16135142975314812936232285)
  ·
    refine ⟨6050678615743054851087107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16135142975314812936232285 6050678615743054851087107)
    ·
      refine ⟨9076017923614582276630661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6050678615743054851087107 9076017923614582276630661)
      ·
        refine ⟨1701753360677734176868249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9076017923614582276630661 1701753360677734176868249)
        ·
          refine ⟨1276315020508300632651187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1701753360677734176868249 1276315020508300632651187)
          ·
            refine ⟨1914472530762450948976781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1276315020508300632651187 1914472530762450948976781)
            ·
              refine ⟨717927199035919105866293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1914472530762450948976781 717927199035919105866293)
              ·
                refine ⟨67305674909617416174965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 717927199035919105866293 67305674909617416174965)
                ·
                  rfl

theorem cell21_884772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 3, 5].length) (baseStart_884772 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_884772 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_884772 prefixEnd_884772 := by exact prefixLift 884772
  have htrace : WordTrace (prefixWord ++ tailWord_884772) baseStart_884772 baseEnd_884772 := by
    simpa [prefixWord, tailWord_884772, baseEnd_884772] using wordTrace_append hprefix tailTrace_884772
  have hstable : (prefixWord ++ tailWord_884772).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_884772).length < 2 ^ (prefixWord ++ tailWord_884772).sum := by decide
  have hdescent : baseEnd_884772 < baseStart_884772 := by decide
  rcases family_descends (prefixWord ++ tailWord_884772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_884786 : List Nat := [3, 2, 1, 1, 2, 3, 1, 5, 3]
def baseStart_884786 : Nat := 118140960795 + 884786 * 2 ^ 59
def prefixEnd_884786 : Nat := 4983230072969 + 3 ^ 40 * 884786 * 2
def baseEnd_884786 : Nat := 201920219719591335291533

theorem tailTrace_884786 : CollatzResearch.WordTrace tailWord_884786 prefixEnd_884786 201920219719591335291533 := by
  unfold tailWord_884786
  simp only [CollatzResearch.WordTrace]
  refine ⟨8067699143144726565868553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21513864381719270842316141 8067699143144726565868553)
  ·
    refine ⟨6050774357358544924401415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8067699143144726565868553 6050774357358544924401415)
    ·
      refine ⟨9076161536037817386602123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6050774357358544924401415 9076161536037817386602123)
      ·
        refine ⟨13614242304056726079903185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9076161536037817386602123 13614242304056726079903185)
        ·
          refine ⟨10210681728042544559927389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13614242304056726079903185 10210681728042544559927389)
          ·
            refine ⟨3829005648015954209972771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10210681728042544559927389 3829005648015954209972771)
            ·
              refine ⟨5743508472023931314959157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3829005648015954209972771 5743508472023931314959157)
              ·
                refine ⟨538453919252243560777421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5743508472023931314959157 538453919252243560777421)
                ·
                  refine ⟨201920219719591335291533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 538453919252243560777421 201920219719591335291533)
                  ·
                    rfl

theorem cell21_884786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 5, 3].length) (baseStart_884786 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_884786 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_884786 prefixEnd_884786 := by exact prefixLift 884786
  have htrace : WordTrace (prefixWord ++ tailWord_884786) baseStart_884786 baseEnd_884786 := by
    simpa [prefixWord, tailWord_884786, baseEnd_884786] using wordTrace_append hprefix tailTrace_884786
  have hstable : (prefixWord ++ tailWord_884786).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_884786).length < 2 ^ (prefixWord ++ tailWord_884786).sum := by decide
  have hdescent : baseEnd_884786 < baseStart_884786 := by decide
  rcases family_descends (prefixWord ++ tailWord_884786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_884800 : List Nat := [2, 1, 1, 2, 2, 4, 3, 2, 4]
def baseStart_884800 : Nat := 118140960795 + 884800 * 2 ^ 59
def prefixEnd_884800 : Nat := 4983230072969 + 3 ^ 40 * 884800 * 2
def baseEnd_884800 : Nat := 201923414710330422058171

theorem tailTrace_884800 : CollatzResearch.WordTrace tailWord_884800 prefixEnd_884800 201923414710330422058171 := by
  unfold tailWord_884800
  simp only [CollatzResearch.WordTrace]
  refine ⟨16135653597264093327241927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21514204796352124436322569 16135653597264093327241927)
  ·
    refine ⟨24203480395896139990862891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16135653597264093327241927 24203480395896139990862891)
    ·
      refine ⟨36305220593844209986294337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24203480395896139990862891 36305220593844209986294337)
      ·
        refine ⟨27228915445383157489720753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36305220593844209986294337 27228915445383157489720753)
        ·
          refine ⟨20421686584037368117290565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27228915445383157489720753 20421686584037368117290565)
          ·
            refine ⟨3829066234507006521991981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20421686584037368117290565 3829066234507006521991981)
            ·
              refine ⟨1435899837940127445746993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3829066234507006521991981 1435899837940127445746993)
              ·
                refine ⟨1076924878455095584310245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1435899837940127445746993 1076924878455095584310245)
                ·
                  refine ⟨201923414710330422058171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1076924878455095584310245 201923414710330422058171)
                  ·
                    rfl

theorem cell21_884800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 3, 2, 4].length) (baseStart_884800 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_884800 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_884800 prefixEnd_884800 := by exact prefixLift 884800
  have htrace : WordTrace (prefixWord ++ tailWord_884800) baseStart_884800 baseEnd_884800 := by
    simpa [prefixWord, tailWord_884800, baseEnd_884800] using wordTrace_append hprefix tailTrace_884800
  have hstable : (prefixWord ++ tailWord_884800).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_884800).length < 2 ^ (prefixWord ++ tailWord_884800).sum := by decide
  have hdescent : baseEnd_884800 < baseStart_884800 := by decide
  rcases family_descends (prefixWord ++ tailWord_884800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_884913 : List Nat := [1, 2, 2, 5, 3, 1, 2, 2, 3]
def baseStart_884913 : Nat := 118140960795 + 884913 * 2 ^ 59
def prefixEnd_884913 : Nat := 4983230072969 + 3 ^ 40 * 884913 * 2
def baseEnd_884913 : Nat := 201949202849867336674607

theorem tailTrace_884913 : CollatzResearch.WordTrace tailWord_884913 prefixEnd_884913 201949202849867336674607 := by
  unfold tailWord_884913
  simp only [CollatzResearch.WordTrace]
  refine ⟨32275428643118806953347393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21516952428745871302231595 32275428643118806953347393)
  ·
    refine ⟨24206571482339105215010545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32275428643118806953347393 24206571482339105215010545)
    ·
      refine ⟨18154928611754328911257909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24206571482339105215010545 18154928611754328911257909)
      ·
        refine ⟨1702024557351968335430429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 18154928611754328911257909 1702024557351968335430429)
        ·
          refine ⟨638259209006988125786411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1702024557351968335430429 638259209006988125786411)
          ·
            refine ⟨957388813510482188679617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 638259209006988125786411 957388813510482188679617)
            ·
              refine ⟨718041610132861641509713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 957388813510482188679617 718041610132861641509713)
              ·
                refine ⟨538531207599646231132285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 718041610132861641509713 538531207599646231132285)
                ·
                  refine ⟨201949202849867336674607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 538531207599646231132285 201949202849867336674607)
                  ·
                    rfl

theorem cell21_884913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 2, 2, 3].length) (baseStart_884913 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_884913 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_884913 prefixEnd_884913 := by exact prefixLift 884913
  have htrace : WordTrace (prefixWord ++ tailWord_884913) baseStart_884913 baseEnd_884913 := by
    simpa [prefixWord, tailWord_884913, baseEnd_884913] using wordTrace_append hprefix tailTrace_884913
  have hstable : (prefixWord ++ tailWord_884913).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_884913).length < 2 ^ (prefixWord ++ tailWord_884913).sum := by decide
  have hdescent : baseEnd_884913 < baseStart_884913 := by decide
  rcases family_descends (prefixWord ++ tailWord_884913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_884924 : List Nat := [2, 2, 2, 3, 4, 1, 1, 6]
def baseStart_884924 : Nat := 118140960795 + 884924 * 2 ^ 59
def prefixEnd_884924 : Nat := 4983230072969 + 3 ^ 40 * 884924 * 2
def baseEnd_884924 : Nat := 67317237733244587330417

theorem tailTrace_884924 : CollatzResearch.WordTrace tailWord_884924 prefixEnd_884924 67317237733244587330417 := by
  unfold tailWord_884924
  simp only [CollatzResearch.WordTrace]
  refine ⟨16137914923039477915998913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21517219897385970554665217 16137914923039477915998913)
  ·
    refine ⟨12103436192279608436999185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16137914923039477915998913 12103436192279608436999185)
    ·
      refine ⟨9077577144209706327749389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12103436192279608436999185 9077577144209706327749389)
      ·
        refine ⟨3404091429078639872906021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9077577144209706327749389 3404091429078639872906021)
        ·
          refine ⟨638267142952244976169879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3404091429078639872906021 638267142952244976169879)
          ·
            refine ⟨957400714428367464254819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 638267142952244976169879 957400714428367464254819)
            ·
              refine ⟨1436101071642551196382229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 957400714428367464254819 1436101071642551196382229)
              ·
                refine ⟨67317237733244587330417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1436101071642551196382229 67317237733244587330417)
                ·
                  rfl

theorem cell21_884924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 1, 6].length) (baseStart_884924 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_884924 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_884924 prefixEnd_884924 := by exact prefixLift 884924
  have htrace : WordTrace (prefixWord ++ tailWord_884924) baseStart_884924 baseEnd_884924 := by
    simpa [prefixWord, tailWord_884924, baseEnd_884924] using wordTrace_append hprefix tailTrace_884924
  have hstable : (prefixWord ++ tailWord_884924).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_884924).length < 2 ^ (prefixWord ++ tailWord_884924).sum := by decide
  have hdescent : baseEnd_884924 < baseStart_884924 := by decide
  rcases family_descends (prefixWord ++ tailWord_884924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_885025 : List Nat := [1, 2, 3, 2, 1, 1, 11]
def baseStart_885025 : Nat := 118140960795 + 885025 * 2 ^ 59
def prefixEnd_885025 : Nat := 4983230072969 + 3 ^ 40 * 885025 * 2
def baseEnd_885025 : Nat := 22441640308420003423079

theorem tailTrace_885025 : CollatzResearch.WordTrace tailWord_885025 prefixEnd_885025 22441640308420003423079 := by
  unfold tailWord_885025
  simp only [CollatzResearch.WordTrace]
  refine ⟨32279513618713050081424529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21519675745808700054283019 32279513618713050081424529)
  ·
    refine ⟨24209635214034787561068397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32279513618713050081424529 24209635214034787561068397)
    ·
      refine ⟨9078613205263045335400649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24209635214034787561068397 9078613205263045335400649)
      ·
        refine ⟨6808959903947284001550487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9078613205263045335400649 6808959903947284001550487)
        ·
          refine ⟨10213439855920926002325731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6808959903947284001550487 10213439855920926002325731)
          ·
            refine ⟨15320159783881389003488597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10213439855920926002325731 15320159783881389003488597)
            ·
              refine ⟨22441640308420003423079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 15320159783881389003488597 22441640308420003423079)
              ·
                rfl

theorem cell21_885025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 11].length) (baseStart_885025 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_885025 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_885025 prefixEnd_885025 := by exact prefixLift 885025
  have htrace : WordTrace (prefixWord ++ tailWord_885025) baseStart_885025 baseEnd_885025 := by
    simpa [prefixWord, tailWord_885025, baseEnd_885025] using wordTrace_append hprefix tailTrace_885025
  have hstable : (prefixWord ++ tailWord_885025).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_885025).length < 2 ^ (prefixWord ++ tailWord_885025).sum := by decide
  have hdescent : baseEnd_885025 < baseStart_885025 := by decide
  rcases family_descends (prefixWord ++ tailWord_885025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_885087 : List Nat := [1, 1, 2, 3, 1, 2, 3, 4, 4]
def baseStart_885087 : Nat := 118140960795 + 885087 * 2 ^ 59
def prefixEnd_885087 : Nat := 4983230072969 + 3 ^ 40 * 885087 * 2
def baseEnd_885087 : Nat := 201988912020481700774251

theorem tailTrace_885087 : CollatzResearch.WordTrace tailWord_885087 prefixEnd_885087 201988912020481700774251 := by
  unfold tailWord_885087
  simp only [CollatzResearch.WordTrace]
  refine ⟨32281774944488434670181515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21521183296325623113454343 32281774944488434670181515)
  ·
    refine ⟨48422662416732652005272273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32281774944488434670181515 48422662416732652005272273)
    ·
      refine ⟨36316996812549489003954205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48422662416732652005272273 36316996812549489003954205)
      ·
        refine ⟨13618873804706058376482827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36316996812549489003954205 13618873804706058376482827)
        ·
          refine ⟨20428310707059087564724241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13618873804706058376482827 20428310707059087564724241)
          ·
            refine ⟨15321233030294315673543181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20428310707059087564724241 15321233030294315673543181)
            ·
              refine ⟨5745462386360368377578693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15321233030294315673543181 5745462386360368377578693)
              ·
                refine ⟨1077274197442569070796005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5745462386360368377578693 1077274197442569070796005)
                ·
                  refine ⟨201988912020481700774251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1077274197442569070796005 201988912020481700774251)
                  ·
                    rfl

theorem cell21_885087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 4, 4].length) (baseStart_885087 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_885087 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_885087 prefixEnd_885087 := by exact prefixLift 885087
  have htrace : WordTrace (prefixWord ++ tailWord_885087) baseStart_885087 baseEnd_885087 := by
    simpa [prefixWord, tailWord_885087, baseEnd_885087] using wordTrace_append hprefix tailTrace_885087
  have hstable : (prefixWord ++ tailWord_885087).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_885087).length < 2 ^ (prefixWord ++ tailWord_885087).sum := by decide
  have hdescent : baseEnd_885087 < baseStart_885087 := by decide
  rcases family_descends (prefixWord ++ tailWord_885087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_885259 : List Nat := [1, 1, 1, 1, 7, 3, 2, 2, 3]
def baseStart_885259 : Nat := 118140960795 + 885259 * 2 ^ 59
def prefixEnd_885259 : Nat := 4983230072969 + 3 ^ 40 * 885259 * 2
def baseEnd_885259 : Nat := 202028164763847623907233

theorem tailTrace_885259 : CollatzResearch.WordTrace tailWord_885259 prefixEnd_885259 202028164763847623907233 := by
  unfold tailWord_885259
  simp only [CollatzResearch.WordTrace]
  refine ⟨32288048299865308045442831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21525365533243538696961887 32288048299865308045442831)
  ·
    refine ⟨48432072449797962068164247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32288048299865308045442831 48432072449797962068164247)
    ·
      refine ⟨72648108674696943102246371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48432072449797962068164247 72648108674696943102246371)
      ·
        refine ⟨108972163012045414653369557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72648108674696943102246371 108972163012045414653369557)
        ·
          refine ⟨2554035070594814405938349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 108972163012045414653369557 2554035070594814405938349)
          ·
            refine ⟨957763151473055402226881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2554035070594814405938349 957763151473055402226881)
            ·
              refine ⟨718322363604791551670161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 957763151473055402226881 718322363604791551670161)
              ·
                refine ⟨538741772703593663752621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 718322363604791551670161 538741772703593663752621)
                ·
                  refine ⟨202028164763847623907233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 538741772703593663752621 202028164763847623907233)
                  ·
                    rfl

theorem cell21_885259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 2, 2, 3].length) (baseStart_885259 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_885259 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_885259 prefixEnd_885259 := by exact prefixLift 885259
  have htrace : WordTrace (prefixWord ++ tailWord_885259) baseStart_885259 baseEnd_885259 := by
    simpa [prefixWord, tailWord_885259, baseEnd_885259] using wordTrace_append hprefix tailTrace_885259
  have hstable : (prefixWord ++ tailWord_885259).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_885259).length < 2 ^ (prefixWord ++ tailWord_885259).sum := by decide
  have hdescent : baseEnd_885259 < baseStart_885259 := by decide
  rcases family_descends (prefixWord ++ tailWord_885259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_885293 : List Nat := [1, 5, 4, 1, 1, 1, 2, 3, 3]
def baseStart_885293 : Nat := 118140960795 + 885293 * 2 ^ 59
def prefixEnd_885293 : Nat := 4983230072969 + 3 ^ 40 * 885293 * 2
def baseEnd_885293 : Nat := 202035924027071120340497

theorem tailTrace_885293 : CollatzResearch.WordTrace tailWord_885293 prefixEnd_885293 202035924027071120340497 := by
  unfold tailWord_885293
  simp only [CollatzResearch.WordTrace]
  refine ⟨32289288381742131852180533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21526192254494754568120355 32289288381742131852180533)
  ·
    refine ⟨3027120785788324861141925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 32289288381742131852180533 3027120785788324861141925)
    ·
      refine ⟨567585147335310911464111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3027120785788324861141925 567585147335310911464111)
      ·
        refine ⟨851377721002966367196167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 567585147335310911464111 851377721002966367196167)
        ·
          refine ⟨1277066581504449550794251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 851377721002966367196167 1277066581504449550794251)
          ·
            refine ⟨1915599872256674326191377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1277066581504449550794251 1915599872256674326191377)
            ·
              refine ⟨1436699904192505744643533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1915599872256674326191377 1436699904192505744643533)
              ·
                refine ⟨538762464072189654241325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1436699904192505744643533 538762464072189654241325)
                ·
                  refine ⟨202035924027071120340497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 538762464072189654241325 202035924027071120340497)
                  ·
                    rfl

theorem cell21_885293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 2, 3, 3].length) (baseStart_885293 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_885293 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_885293 prefixEnd_885293 := by exact prefixLift 885293
  have htrace : WordTrace (prefixWord ++ tailWord_885293) baseStart_885293 baseEnd_885293 := by
    simpa [prefixWord, tailWord_885293, baseEnd_885293] using wordTrace_append hprefix tailTrace_885293
  have hstable : (prefixWord ++ tailWord_885293).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_885293).length < 2 ^ (prefixWord ++ tailWord_885293).sum := by decide
  have hdescent : baseEnd_885293 < baseStart_885293 := by decide
  rcases family_descends (prefixWord ++ tailWord_885293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_885318 : List Nat := [6, 1, 1, 1, 2, 1, 1, 3, 5]
def baseStart_885318 : Nat := 118140960795 + 885318 * 2 ^ 59
def prefixEnd_885318 : Nat := 4983230072969 + 3 ^ 40 * 885318 * 2
def baseEnd_885318 : Nat := 202041629367676632423779

theorem tailTrace_885318 : CollatzResearch.WordTrace tailWord_885318 prefixEnd_885318 202041629367676632423779 := by
  unfold tailWord_885318
  simp only [CollatzResearch.WordTrace]
  refine ⟨1009068756457861285057519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 21526800137767707414560405 1009068756457861285057519)
  ·
    refine ⟨1513603134686791927586279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1009068756457861285057519 1513603134686791927586279)
    ·
      refine ⟨2270404702030187891379419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1513603134686791927586279 2270404702030187891379419)
      ·
        refine ⟨3405607053045281837069129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2270404702030187891379419 3405607053045281837069129)
        ·
          refine ⟨2554205289783961377801847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3405607053045281837069129 2554205289783961377801847)
          ·
            refine ⟨3831307934675942066702771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2554205289783961377801847 3831307934675942066702771)
            ·
              refine ⟨5746961902013913100054157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3831307934675942066702771 5746961902013913100054157)
              ·
                refine ⟨2155110713255217412520309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5746961902013913100054157 2155110713255217412520309)
                ·
                  refine ⟨202041629367676632423779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2155110713255217412520309 202041629367676632423779)
                  ·
                    rfl

theorem cell21_885318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 3, 5].length) (baseStart_885318 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_885318 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_885318 prefixEnd_885318 := by exact prefixLift 885318
  have htrace : WordTrace (prefixWord ++ tailWord_885318) baseStart_885318 baseEnd_885318 := by
    simpa [prefixWord, tailWord_885318, baseEnd_885318] using wordTrace_append hprefix tailTrace_885318
  have hstable : (prefixWord ++ tailWord_885318).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_885318).length < 2 ^ (prefixWord ++ tailWord_885318).sum := by decide
  have hdescent : baseEnd_885318 < baseStart_885318 := by decide
  rcases family_descends (prefixWord ++ tailWord_885318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_885352 : List Nat := [2, 1, 4, 3, 3, 1, 1, 3, 3]
def baseStart_885352 : Nat := 118140960795 + 885352 * 2 ^ 59
def prefixEnd_885352 : Nat := 4983230072969 + 3 ^ 40 * 885352 * 2
def baseEnd_885352 : Nat := 202049388630900128857043

theorem tailTrace_885352 : CollatzResearch.WordTrace tailWord_885352 prefixEnd_885352 202049388630900128857043 := by
  unfold tailWord_885352
  simp only [CollatzResearch.WordTrace]
  refine ⟨16145720144264192464289155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21527626859018923285718873 16145720144264192464289155)
  ·
    refine ⟨24218580216396288696433733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16145720144264192464289155 24218580216396288696433733)
    ·
      refine ⟨4540983790574304130581325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24218580216396288696433733 4540983790574304130581325)
      ·
        refine ⟨1702868921465364048967997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4540983790574304130581325 1702868921465364048967997)
        ·
          refine ⟨638575845549511518362999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1702868921465364048967997 638575845549511518362999)
          ·
            refine ⟨957863768324267277544499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 638575845549511518362999 957863768324267277544499)
            ·
              refine ⟨1436795652486400916316749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 957863768324267277544499 1436795652486400916316749)
              ·
                refine ⟨538798369682400343618781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1436795652486400916316749 538798369682400343618781)
                ·
                  refine ⟨202049388630900128857043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 538798369682400343618781 202049388630900128857043)
                  ·
                    rfl

theorem cell21_885352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 1, 3, 3].length) (baseStart_885352 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_885352 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_885352 prefixEnd_885352 := by exact prefixLift 885352
  have htrace : WordTrace (prefixWord ++ tailWord_885352) baseStart_885352 baseEnd_885352 := by
    simpa [prefixWord, tailWord_885352, baseEnd_885352] using wordTrace_append hprefix tailTrace_885352
  have hstable : (prefixWord ++ tailWord_885352).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_885352).length < 2 ^ (prefixWord ++ tailWord_885352).sum := by decide
  have hdescent : baseEnd_885352 < baseStart_885352 := by decide
  rcases family_descends (prefixWord ++ tailWord_885352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_885405 : List Nat := [1, 4, 2, 1, 1, 1, 4, 7]
def baseStart_885405 : Nat := 118140960795 + 885405 * 2 ^ 59
def prefixEnd_885405 : Nat := 4983230072969 + 3 ^ 40 * 885405 * 2
def baseEnd_885405 : Nat := 67353827984327938157867

theorem tailTrace_885405 : CollatzResearch.WordTrace tailWord_885405 prefixEnd_885405 67353827984327938157867 := by
  unfold tailWord_885405
  simp only [CollatzResearch.WordTrace]
  refine ⟨32293373357336374980257669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21528915571557583320171779 32293373357336374980257669)
  ·
    refine ⟨6055007504500570308798313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32293373357336374980257669 6055007504500570308798313)
    ·
      refine ⟨4541255628375427731598735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6055007504500570308798313 4541255628375427731598735)
      ·
        refine ⟨6811883442563141597398103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4541255628375427731598735 6811883442563141597398103)
        ·
          refine ⟨10217825163844712396097155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6811883442563141597398103 10217825163844712396097155)
          ·
            refine ⟨15326737745767068594145733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10217825163844712396097155 15326737745767068594145733)
            ·
              refine ⟨2873763327331325361402325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15326737745767068594145733 2873763327331325361402325)
              ·
                refine ⟨67353827984327938157867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2873763327331325361402325 67353827984327938157867)
                ·
                  rfl

theorem cell21_885405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 4, 7].length) (baseStart_885405 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_885405 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_885405 prefixEnd_885405 := by exact prefixLift 885405
  have htrace : WordTrace (prefixWord ++ tailWord_885405) baseStart_885405 baseEnd_885405 := by
    simpa [prefixWord, tailWord_885405, baseEnd_885405] using wordTrace_append hprefix tailTrace_885405
  have hstable : (prefixWord ++ tailWord_885405).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_885405).length < 2 ^ (prefixWord ++ tailWord_885405).sum := by decide
  have hdescent : baseEnd_885405 < baseStart_885405 := by decide
  rcases family_descends (prefixWord ++ tailWord_885405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_885422 : List Nat := [4, 1, 4, 1, 1, 10]
def baseStart_885422 : Nat := 118140960795 + 885422 * 2 ^ 59
def prefixEnd_885422 : Nat := 4983230072969 + 3 ^ 40 * 885422 * 2
def baseEnd_885422 : Nat := 7483902354985020840379

theorem tailTrace_885422 : CollatzResearch.WordTrace tailWord_885422 prefixEnd_885422 7483902354985020840379 := by
  unfold tailWord_885422
  simp only [CollatzResearch.WordTrace]
  refine ⟨4036749174784348360453315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21529328932183191255751013 4036749174784348360453315)
  ·
    refine ⟨6055123762176522540679973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4036749174784348360453315 6055123762176522540679973)
    ·
      refine ⟨1135335705408097976377495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6055123762176522540679973 1135335705408097976377495)
      ·
        refine ⟨1703003558112146964566243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1135335705408097976377495 1703003558112146964566243)
        ·
          refine ⟨2554505337168220446849365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1703003558112146964566243 2554505337168220446849365)
          ·
            refine ⟨7483902354985020840379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2554505337168220446849365 7483902354985020840379)
            ·
              rfl

theorem cell21_885422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 10].length) (baseStart_885422 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_885422 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_885422 prefixEnd_885422 := by exact prefixLift 885422
  have htrace : WordTrace (prefixWord ++ tailWord_885422) baseStart_885422 baseEnd_885422 := by
    simpa [prefixWord, tailWord_885422, baseEnd_885422] using wordTrace_append hprefix tailTrace_885422
  have hstable : (prefixWord ++ tailWord_885422).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_885422).length < 2 ^ (prefixWord ++ tailWord_885422).sum := by decide
  have hdescent : baseEnd_885422 < baseStart_885422 := by decide
  rcases family_descends (prefixWord ++ tailWord_885422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_885425 : List Nat := [1, 2, 2, 6, 1, 1, 2, 2, 4]
def baseStart_885425 : Nat := 118140960795 + 885425 * 2 ^ 59
def prefixEnd_885425 : Nat := 4983230072969 + 3 ^ 40 * 885425 * 2
def baseEnd_885425 : Nat := 202066048225468224140227

theorem tailTrace_885425 : CollatzResearch.WordTrace tailWord_885425 prefixEnd_885425 202066048225468224140227 := by
  unfold tailWord_885425
  simp only [CollatzResearch.WordTrace]
  refine ⟨32294102817263918395985729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21529401878175945597323819 32294102817263918395985729)
  ·
    refine ⟨24220577112947938796989297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32294102817263918395985729 24220577112947938796989297)
    ·
      refine ⟨18165432834710954097741973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24220577112947938796989297 18165432834710954097741973)
      ·
        refine ⟨851504664127075973331655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 18165432834710954097741973 851504664127075973331655)
        ·
          refine ⟨1277256996190613959997483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 851504664127075973331655 1277256996190613959997483)
          ·
            refine ⟨1915885494285920939996225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1277256996190613959997483 1915885494285920939996225)
            ·
              refine ⟨1436914120714440704997169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1915885494285920939996225 1436914120714440704997169)
              ·
                refine ⟨1077685590535830528747877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1436914120714440704997169 1077685590535830528747877)
                ·
                  refine ⟨202066048225468224140227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1077685590535830528747877 202066048225468224140227)
                  ·
                    rfl

theorem cell21_885425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 2, 2, 4].length) (baseStart_885425 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_885425 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_885425 prefixEnd_885425 := by exact prefixLift 885425
  have htrace : WordTrace (prefixWord ++ tailWord_885425) baseStart_885425 baseEnd_885425 := by
    simpa [prefixWord, tailWord_885425, baseEnd_885425] using wordTrace_append hprefix tailTrace_885425
  have hstable : (prefixWord ++ tailWord_885425).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_885425).length < 2 ^ (prefixWord ++ tailWord_885425).sum := by decide
  have hdescent : baseEnd_885425 < baseStart_885425 := by decide
  rcases family_descends (prefixWord ++ tailWord_885425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_885436 : List Nat := [2, 2, 2, 3, 1, 1, 2, 3, 5]
def baseStart_885436 : Nat := 118140960795 + 885436 * 2 ^ 59
def prefixEnd_885436 : Nat := 4983230072969 + 3 ^ 40 * 885436 * 2
def baseEnd_885436 : Nat := 202068558575334649456871

theorem tailTrace_885436 : CollatzResearch.WordTrace tailWord_885436 prefixEnd_885436 202068558575334649456871 := by
  unfold tailWord_885436
  simp only [CollatzResearch.WordTrace]
  refine ⟨16147252010112033637318081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21529669346816044849757441 16147252010112033637318081)
  ·
    refine ⟨12110439007584025227988561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16147252010112033637318081 12110439007584025227988561)
    ·
      refine ⟨9082829255688018920991421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12110439007584025227988561 9082829255688018920991421)
      ·
        refine ⟨3406060970883007095371783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9082829255688018920991421 3406060970883007095371783)
        ·
          refine ⟨5109091456324510643057675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3406060970883007095371783 5109091456324510643057675)
          ·
            refine ⟨7663637184486765964586513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5109091456324510643057675 7663637184486765964586513)
            ·
              refine ⟨5747727888365074473439885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7663637184486765964586513 5747727888365074473439885)
              ·
                refine ⟨2155397958136902927539957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5747727888365074473439885 2155397958136902927539957)
                ·
                  refine ⟨202068558575334649456871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2155397958136902927539957 202068558575334649456871)
                  ·
                    rfl

theorem cell21_885436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 3, 5].length) (baseStart_885436 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_885436 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_885436 prefixEnd_885436 := by exact prefixLift 885436
  have htrace : WordTrace (prefixWord ++ tailWord_885436) baseStart_885436 baseEnd_885436 := by
    simpa [prefixWord, tailWord_885436, baseEnd_885436] using wordTrace_append hprefix tailTrace_885436
  have hstable : (prefixWord ++ tailWord_885436).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_885436).length < 2 ^ (prefixWord ++ tailWord_885436).sum := by decide
  have hdescent : baseEnd_885436 < baseStart_885436 := by decide
  rcases family_descends (prefixWord ++ tailWord_885436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_885512 : List Nat := [2, 1, 3, 2, 2, 2, 2, 2, 5]
def baseStart_885512 : Nat := 118140960795 + 885512 * 2 ^ 59
def prefixEnd_885512 : Nat := 4983230072969 + 3 ^ 40 * 885512 * 2
def baseEnd_885512 : Nat := 202085902810775406190049

theorem tailTrace_885512 : CollatzResearch.WordTrace tailWord_885512 prefixEnd_885512 202085902810775406190049 := by
  unfold tailWord_885512
  simp only [CollatzResearch.WordTrace]
  refine ⟨16148637983974366127201395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21531517311965821502935193 16148637983974366127201395)
  ·
    refine ⟨24222956975961549190802093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16148637983974366127201395 24222956975961549190802093)
    ·
      refine ⟨9083608865985580946550785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24222956975961549190802093 9083608865985580946550785)
      ·
        refine ⟨6812706649489185709913089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9083608865985580946550785 6812706649489185709913089)
        ·
          refine ⟨5109529987116889282434817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6812706649489185709913089 5109529987116889282434817)
          ·
            refine ⟨3832147490337666961826113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5109529987116889282434817 3832147490337666961826113)
            ·
              refine ⟨2874110617753250221369585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3832147490337666961826113 2874110617753250221369585)
              ·
                refine ⟨2155582963314937666027189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2874110617753250221369585 2155582963314937666027189)
                ·
                  refine ⟨202085902810775406190049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2155582963314937666027189 202085902810775406190049)
                  ·
                    rfl

theorem cell21_885512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 2, 2, 5].length) (baseStart_885512 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_885512 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_885512 prefixEnd_885512 := by exact prefixLift 885512
  have htrace : WordTrace (prefixWord ++ tailWord_885512) baseStart_885512 baseEnd_885512 := by
    simpa [prefixWord, tailWord_885512, baseEnd_885512] using wordTrace_append hprefix tailTrace_885512
  have hstable : (prefixWord ++ tailWord_885512).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_885512).length < 2 ^ (prefixWord ++ tailWord_885512).sum := by decide
  have hdescent : baseEnd_885512 < baseStart_885512 := by decide
  rcases family_descends (prefixWord ++ tailWord_885512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_885557 : List Nat := [1, 3, 3, 1, 3, 1, 1, 8]
def baseStart_885557 : Nat := 118140960795 + 885557 * 2 ^ 59
def prefixEnd_885557 : Nat := 4983230072969 + 3 ^ 40 * 885557 * 2
def baseEnd_885557 : Nat := 67365390807955109313319

theorem tailTrace_885557 : CollatzResearch.WordTrace tailWord_885557 prefixEnd_885557 67365390807955109313319 := by
  unfold tailWord_885557
  simp only [CollatzResearch.WordTrace]
  refine ⟨32298917252785704939790925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21532611501857136626527283 32298917252785704939790925)
  ·
    refine ⟨12112093969794639352421597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32298917252785704939790925 12112093969794639352421597)
    ·
      refine ⟨4542035238672989757158099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12112093969794639352421597 4542035238672989757158099)
      ·
        refine ⟨6813052858009484635737149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4542035238672989757158099 6813052858009484635737149)
        ·
          refine ⟨2554894821753556738401431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6813052858009484635737149 2554894821753556738401431)
          ·
            refine ⟨3832342232630335107602147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2554894821753556738401431 3832342232630335107602147)
            ·
              refine ⟨5748513348945502661403221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3832342232630335107602147 5748513348945502661403221)
              ·
                refine ⟨67365390807955109313319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5748513348945502661403221 67365390807955109313319)
                ·
                  rfl

theorem cell21_885557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 8].length) (baseStart_885557 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_885557 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_885557 prefixEnd_885557 := by exact prefixLift 885557
  have htrace : WordTrace (prefixWord ++ tailWord_885557) baseStart_885557 baseEnd_885557 := by
    simpa [prefixWord, tailWord_885557, baseEnd_885557] using wordTrace_append hprefix tailTrace_885557
  have hstable : (prefixWord ++ tailWord_885557).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_885557).length < 2 ^ (prefixWord ++ tailWord_885557).sum := by decide
  have hdescent : baseEnd_885557 < baseStart_885557 := by decide
  rcases family_descends (prefixWord ++ tailWord_885557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_885571 : List Nat := [1, 1, 1, 3, 1, 4, 2, 1, 7]
def baseStart_885571 : Nat := 118140960795 + 885571 * 2 ^ 59
def prefixEnd_885571 : Nat := 4983230072969 + 3 ^ 40 * 885571 * 2
def baseEnd_885571 : Nat := 202099367414604414706595

theorem tailTrace_885571 : CollatzResearch.WordTrace tailWord_885571 prefixEnd_885571 202099367414604414706595 := by
  unfold tailWord_885571
  simp only [CollatzResearch.WordTrace]
  refine ⟨32299427874734985330800567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21532951916489990220533711 32299427874734985330800567)
  ·
    refine ⟨48449141812102477996200851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32299427874734985330800567 48449141812102477996200851)
    ·
      refine ⟨72673712718153716994301277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48449141812102477996200851 72673712718153716994301277)
      ·
        refine ⟨27252642269307643872862979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72673712718153716994301277 27252642269307643872862979)
        ·
          refine ⟨40878963403961465809294469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27252642269307643872862979 40878963403961465809294469)
          ·
            refine ⟨7664805638242774839242713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40878963403961465809294469 7664805638242774839242713)
            ·
              refine ⟨5748604228682081129432035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7664805638242774839242713 5748604228682081129432035)
              ·
                refine ⟨8622906343023121694148053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5748604228682081129432035 8622906343023121694148053)
                ·
                  refine ⟨202099367414604414706595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8622906343023121694148053 202099367414604414706595)
                  ·
                    rfl

theorem cell21_885571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 1, 7].length) (baseStart_885571 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_885571 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_885571 prefixEnd_885571 := by exact prefixLift 885571
  have htrace : WordTrace (prefixWord ++ tailWord_885571) baseStart_885571 baseEnd_885571 := by
    simpa [prefixWord, tailWord_885571, baseEnd_885571] using wordTrace_append hprefix tailTrace_885571
  have hstable : (prefixWord ++ tailWord_885571).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_885571).length < 2 ^ (prefixWord ++ tailWord_885571).sum := by decide
  have hdescent : baseEnd_885571 < baseStart_885571 := by decide
  rcases family_descends (prefixWord ++ tailWord_885571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_885650 : List Nat := [3, 2, 3, 2, 2, 1, 8]
def baseStart_885650 : Nat := 118140960795 + 885650 * 2 ^ 59
def prefixEnd_885650 : Nat := 4983230072969 + 3 ^ 40 * 885650 * 2
def baseEnd_885650 : Nat := 22457488476768648098863

theorem tailTrace_885650 : CollatzResearch.WordTrace tailWord_885650 prefixEnd_885650 22457488476768648098863 := by
  unfold tailWord_885650
  simp only [CollatzResearch.WordTrace]
  refine ⟨8075577310362195455731601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21534872827632521215284269 8075577310362195455731601)
  ·
    refine ⟨6056682982771646591798701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8075577310362195455731601 6056682982771646591798701)
    ·
      refine ⟨2271256118539367471924513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6056682982771646591798701 2271256118539367471924513)
      ·
        refine ⟨1703442088904525603943385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2271256118539367471924513 1703442088904525603943385)
        ·
          refine ⟨1277581566678394202957539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1703442088904525603943385 1277581566678394202957539)
          ·
            refine ⟨1916372350017591304436309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1277581566678394202957539 1916372350017591304436309)
            ·
              refine ⟨22457488476768648098863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1916372350017591304436309 22457488476768648098863)
              ·
                rfl

theorem cell21_885650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 8].length) (baseStart_885650 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_885650 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_885650 prefixEnd_885650 := by exact prefixLift 885650
  have htrace : WordTrace (prefixWord ++ tailWord_885650) baseStart_885650 baseEnd_885650 := by
    simpa [prefixWord, tailWord_885650, baseEnd_885650] using wordTrace_append hprefix tailTrace_885650
  have hstable : (prefixWord ++ tailWord_885650).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_885650).length < 2 ^ (prefixWord ++ tailWord_885650).sum := by decide
  have hdescent : baseEnd_885650 < baseStart_885650 := by decide
  rcases family_descends (prefixWord ++ tailWord_885650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_885684 : List Nat := [2, 5, 2, 1, 1, 3, 2, 5]
def baseStart_885684 : Nat := 118140960795 + 885684 * 2 ^ 59
def prefixEnd_885684 : Nat := 4983230072969 + 3 ^ 40 * 885684 * 2
def baseEnd_885684 : Nat := 67375051851380443107677

theorem tailTrace_885684 : CollatzResearch.WordTrace tailWord_885684 prefixEnd_885684 67375051851380443107677 := by
  unfold tailWord_885684
  simp only [CollatzResearch.WordTrace]
  refine ⟨16151774661662802814832053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21535699548883737086442737 16151774661662802814832053)
  ·
    refine ⟨1514228874530887763890505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16151774661662802814832053 1514228874530887763890505)
    ·
      refine ⟨1135671655898165822917879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1514228874530887763890505 1135671655898165822917879)
      ·
        refine ⟨1703507483847248734376819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1135671655898165822917879 1703507483847248734376819)
        ·
          refine ⟨2555261225770873101565229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1703507483847248734376819 2555261225770873101565229)
          ·
            refine ⟨958222959664077413086961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2555261225770873101565229 958222959664077413086961)
            ·
              refine ⟨718667219748058059815221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 958222959664077413086961 718667219748058059815221)
              ·
                refine ⟨67375051851380443107677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 718667219748058059815221 67375051851380443107677)
                ·
                  rfl

theorem cell21_885684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 2, 5].length) (baseStart_885684 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_885684 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_885684 prefixEnd_885684 := by exact prefixLift 885684
  have htrace : WordTrace (prefixWord ++ tailWord_885684) baseStart_885684 baseEnd_885684 := by
    simpa [prefixWord, tailWord_885684, baseEnd_885684] using wordTrace_append hprefix tailTrace_885684
  have hstable : (prefixWord ++ tailWord_885684).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_885684).length < 2 ^ (prefixWord ++ tailWord_885684).sum := by decide
  have hdescent : baseEnd_885684 < baseStart_885684 := by decide
  rcases family_descends (prefixWord ++ tailWord_885684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_885768 : List Nat := [2, 1, 3, 2, 1, 12]
def baseStart_885768 : Nat := 118140960795 + 885768 * 2 ^ 59
def prefixEnd_885768 : Nat := 4983230072969 + 3 ^ 40 * 885768 * 2
def baseEnd_885768 : Nat := 7486826870317624071217

theorem tailTrace_885768 : CollatzResearch.WordTrace tailWord_885768 prefixEnd_885768 7486826870317624071217 := by
  unfold tailWord_885768
  simp only [CollatzResearch.WordTrace]
  refine ⟨16153306527510643987860979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21537742036680858650481305 16153306527510643987860979)
  ·
    refine ⟨24229959791265965981791469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16153306527510643987860979 24229959791265965981791469)
    ·
      refine ⟨9086234921724737243171801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24229959791265965981791469 9086234921724737243171801)
      ·
        refine ⟨6814676191293552932378851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9086234921724737243171801 6814676191293552932378851)
        ·
          refine ⟨10222014286940329398568277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6814676191293552932378851 10222014286940329398568277)
          ·
            refine ⟨7486826870317624071217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 10222014286940329398568277 7486826870317624071217)
            ·
              rfl

theorem cell21_885768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 12].length) (baseStart_885768 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_885768 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_885768 prefixEnd_885768 := by exact prefixLift 885768
  have htrace : WordTrace (prefixWord ++ tailWord_885768) baseStart_885768 baseEnd_885768 := by
    simpa [prefixWord, tailWord_885768, baseEnd_885768] using wordTrace_append hprefix tailTrace_885768
  have hstable : (prefixWord ++ tailWord_885768).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_885768).length < 2 ^ (prefixWord ++ tailWord_885768).sum := by decide
  have hdescent : baseEnd_885768 < baseStart_885768 := by decide
  rcases family_descends (prefixWord ++ tailWord_885768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_885771 : List Nat := [1, 1, 1, 1, 6, 3, 2, 2, 4]
def baseStart_885771 : Nat := 118140960795 + 885771 * 2 ^ 59
def prefixEnd_885771 : Nat := 4983230072969 + 3 ^ 40 * 885771 * 2
def baseEnd_885771 : Nat := 202145010139448511372853

theorem tailTrace_885771 : CollatzResearch.WordTrace tailWord_885771 prefixEnd_885771 202145010139448511372853 := by
  unfold tailWord_885771
  simp only [CollatzResearch.WordTrace]
  refine ⟨32306722474010419488081167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21537814982673612992054111 32306722474010419488081167)
  ·
    refine ⟨48460083711015629232121751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32306722474010419488081167 48460083711015629232121751)
    ·
      refine ⟨72690125566523443848182627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48460083711015629232121751 72690125566523443848182627)
      ·
        refine ⟨109035188349785165772273941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72690125566523443848182627 109035188349785165772273941)
        ·
          refine ⟨5111024453896179645575341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 109035188349785165772273941 5111024453896179645575341)
          ·
            refine ⟨1916634170211067367090753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5111024453896179645575341 1916634170211067367090753)
            ·
              refine ⟨1437475627658300525318065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1916634170211067367090753 1437475627658300525318065)
              ·
                refine ⟨1078106720743725393988549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1437475627658300525318065 1078106720743725393988549)
                ·
                  refine ⟨202145010139448511372853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1078106720743725393988549 202145010139448511372853)
                  ·
                    rfl

theorem cell21_885771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 2, 2, 4].length) (baseStart_885771 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_885771 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_885771 prefixEnd_885771 := by exact prefixLift 885771
  have htrace : WordTrace (prefixWord ++ tailWord_885771) baseStart_885771 baseEnd_885771 := by
    simpa [prefixWord, tailWord_885771, baseEnd_885771] using wordTrace_append hprefix tailTrace_885771
  have hstable : (prefixWord ++ tailWord_885771).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_885771).length < 2 ^ (prefixWord ++ tailWord_885771).sum := by decide
  have hdescent : baseEnd_885771 < baseStart_885771 := by decide
  rcases family_descends (prefixWord ++ tailWord_885771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_885774 : List Nat := [4, 1, 1, 2, 2, 2, 4, 2, 3]
def baseStart_885774 : Nat := 118140960795 + 885774 * 2 ^ 59
def prefixEnd_885774 : Nat := 4983230072969 + 3 ^ 40 * 885774 * 2
def baseEnd_885774 : Nat := 202145694780321172822847

theorem tailTrace_885774 : CollatzResearch.WordTrace tailWord_885774 prefixEnd_885774 202145694780321172822847 := by
  unfold tailWord_885774
  simp only [CollatzResearch.WordTrace]
  refine ⟨4038353986624943875055047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21537887928666367333626917 4038353986624943875055047)
  ·
    refine ⟨6057530979937415812582571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4038353986624943875055047 6057530979937415812582571)
    ·
      refine ⟨9086296469906123718873857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6057530979937415812582571 9086296469906123718873857)
      ·
        refine ⟨6814722352429592789155393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9086296469906123718873857 6814722352429592789155393)
        ·
          refine ⟨5111041764322194591866545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6814722352429592789155393 5111041764322194591866545)
          ·
            refine ⟨3833281323241645943899909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5111041764322194591866545 3833281323241645943899909)
            ·
              refine ⟨718740248107808614481233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3833281323241645943899909 718740248107808614481233)
              ·
                refine ⟨539055186080856460860925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 718740248107808614481233 539055186080856460860925)
                ·
                  refine ⟨202145694780321172822847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 539055186080856460860925 202145694780321172822847)
                  ·
                    rfl

theorem cell21_885774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 4, 2, 3].length) (baseStart_885774 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_885774 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_885774 prefixEnd_885774 := by exact prefixLift 885774
  have htrace : WordTrace (prefixWord ++ tailWord_885774) baseStart_885774 baseEnd_885774 := by
    simpa [prefixWord, tailWord_885774, baseEnd_885774] using wordTrace_append hprefix tailTrace_885774
  have hstable : (prefixWord ++ tailWord_885774).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_885774).length < 2 ^ (prefixWord ++ tailWord_885774).sum := by decide
  have hdescent : baseEnd_885774 < baseStart_885774 := by decide
  rcases family_descends (prefixWord ++ tailWord_885774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_885892 : List Nat := [2, 3, 2, 1, 2, 2, 3, 1, 5]
def baseStart_885892 : Nat := 118140960795 + 885892 * 2 ^ 59
def prefixEnd_885892 : Nat := 4983230072969 + 3 ^ 40 * 885892 * 2
def baseEnd_885892 : Nat := 202172623987979189855939

theorem tailTrace_885892 : CollatzResearch.WordTrace tailWord_885892 prefixEnd_885892 202172623987979189855939 := by
  unfold tailWord_885892
  simp only [CollatzResearch.WordTrace]
  refine ⟨16155567853286028576617965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21540757137714704768823953 16155567853286028576617965)
  ·
    refine ⟨6058337944982260716231737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16155567853286028576617965 6058337944982260716231737)
    ·
      refine ⟨4543753458736695537173803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6058337944982260716231737 4543753458736695537173803)
      ·
        refine ⟨6815630188105043305760705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4543753458736695537173803 6815630188105043305760705)
        ·
          refine ⟨5111722641078782479320529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6815630188105043305760705 5111722641078782479320529)
          ·
            refine ⟨3833791980809086859490397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5111722641078782479320529 3833791980809086859490397)
            ·
              refine ⟨1437671992803407572308899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3833791980809086859490397 1437671992803407572308899)
              ·
                refine ⟨2156507989205111358463349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1437671992803407572308899 2156507989205111358463349)
                ·
                  refine ⟨202172623987979189855939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2156507989205111358463349 202172623987979189855939)
                  ·
                    rfl

theorem cell21_885892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 3, 1, 5].length) (baseStart_885892 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_885892 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_885892 prefixEnd_885892 := by exact prefixLift 885892
  have htrace : WordTrace (prefixWord ++ tailWord_885892) baseStart_885892 baseEnd_885892 := by
    simpa [prefixWord, tailWord_885892, baseEnd_885892] using wordTrace_append hprefix tailTrace_885892
  have hstable : (prefixWord ++ tailWord_885892).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_885892).length < 2 ^ (prefixWord ++ tailWord_885892).sum := by decide
  have hdescent : baseEnd_885892 < baseStart_885892 := by decide
  rcases family_descends (prefixWord ++ tailWord_885892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_885920 : List Nat := [2, 1, 1, 4, 2, 1, 1, 9]
def baseStart_885920 : Nat := 118140960795 + 885920 * 2 ^ 59
def prefixEnd_885920 : Nat := 4983230072969 + 3 ^ 40 * 885920 * 2
def baseEnd_885920 : Nat := 67393004656485787796405

theorem tailTrace_885920 : CollatzResearch.WordTrace tailWord_885920 prefixEnd_885920 67393004656485787796405 := by
  unfold tailWord_885920
  simp only [CollatzResearch.WordTrace]
  refine ⟨16156078475235308967627607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21541437966980411956836809 16156078475235308967627607)
  ·
    refine ⟨24234117712852963451441411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16156078475235308967627607 24234117712852963451441411)
    ·
      refine ⟨36351176569279445177162117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24234117712852963451441411 36351176569279445177162117)
      ·
        refine ⟨6815845606739895970717897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36351176569279445177162117 6815845606739895970717897)
        ·
          refine ⟨5111884205054921978038423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6815845606739895970717897 5111884205054921978038423)
          ·
            refine ⟨7667826307582382967057635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5111884205054921978038423 7667826307582382967057635)
            ·
              refine ⟨11501739461373574450586453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7667826307582382967057635 11501739461373574450586453)
              ·
                refine ⟨67393004656485787796405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 11501739461373574450586453 67393004656485787796405)
                ·
                  rfl

theorem cell21_885920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 9].length) (baseStart_885920 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_885920 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_885920 prefixEnd_885920 := by exact prefixLift 885920
  have htrace : WordTrace (prefixWord ++ tailWord_885920) baseStart_885920 baseEnd_885920 := by
    simpa [prefixWord, tailWord_885920, baseEnd_885920] using wordTrace_append hprefix tailTrace_885920
  have hstable : (prefixWord ++ tailWord_885920).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_885920).length < 2 ^ (prefixWord ++ tailWord_885920).sum := by decide
  have hdescent : baseEnd_885920 < baseStart_885920 := by decide
  rcases family_descends (prefixWord ++ tailWord_885920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_885985 : List Nat := [1, 2, 3, 1, 3, 3, 2, 3, 3]
def baseStart_885985 : Nat := 118140960795 + 885985 * 2 ^ 59
def prefixEnd_885985 : Nat := 4983230072969 + 3 ^ 40 * 885985 * 2
def baseEnd_885985 : Nat := 202193847855031694805749

theorem tailTrace_885985 : CollatzResearch.WordTrace tailWord_885985 prefixEnd_885985 202193847855031694805749 := by
  unfold tailWord_885985
  simp only [CollatzResearch.WordTrace]
  refine ⟨32314527695235134036371409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21543018463490089357580939 32314527695235134036371409)
  ·
    refine ⟨24235895771426350527278557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32314527695235134036371409 24235895771426350527278557)
    ·
      refine ⟨9088460914284881447729459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24235895771426350527278557 9088460914284881447729459)
      ·
        refine ⟨13632691371427322171594189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9088460914284881447729459 13632691371427322171594189)
        ·
          refine ⟨5112259264285245814347821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13632691371427322171594189 5112259264285245814347821)
          ·
            refine ⟨1917097224106967180380433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5112259264285245814347821 1917097224106967180380433)
            ·
              refine ⟨1437822918080225385285325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1917097224106967180380433 1437822918080225385285325)
              ·
                refine ⟨539183594280084519481997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1437822918080225385285325 539183594280084519481997)
                ·
                  refine ⟨202193847855031694805749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 539183594280084519481997 202193847855031694805749)
                  ·
                    rfl

theorem cell21_885985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 2, 3, 3].length) (baseStart_885985 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_885985 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_885985 prefixEnd_885985 := by exact prefixLift 885985
  have htrace : WordTrace (prefixWord ++ tailWord_885985) baseStart_885985 baseEnd_885985 := by
    simpa [prefixWord, tailWord_885985, baseEnd_885985] using wordTrace_append hprefix tailTrace_885985
  have hstable : (prefixWord ++ tailWord_885985).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_885985).length < 2 ^ (prefixWord ++ tailWord_885985).sum := by decide
  have hdescent : baseEnd_885985 < baseStart_885985 := by decide
  rcases family_descends (prefixWord ++ tailWord_885985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_885996 : List Nat := [2, 2, 1, 1, 2, 5, 8]
def baseStart_885996 : Nat := 118140960795 + 885996 * 2 ^ 59
def prefixEnd_885996 : Nat := 4983230072969 + 3 ^ 40 * 885996 * 2
def baseEnd_885996 : Nat := 22466262022766457791377

theorem tailTrace_885996 : CollatzResearch.WordTrace tailWord_885996 prefixEnd_885996 22466262022766457791377 := by
  unfold tailWord_885996
  simp only [CollatzResearch.WordTrace]
  refine ⟨16157464449097641457510921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21543285932130188610014561 16157464449097641457510921)
  ·
    refine ⟨12118098336823231093133191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16157464449097641457510921 12118098336823231093133191)
    ·
      refine ⟨18177147505234846639699787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12118098336823231093133191 18177147505234846639699787)
      ·
        refine ⟨27265721257852269959549681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18177147505234846639699787 27265721257852269959549681)
        ·
          refine ⟨20449290943389202469662261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27265721257852269959549681 20449290943389202469662261)
          ·
            refine ⟨1917121025942737731530837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 20449290943389202469662261 1917121025942737731530837)
            ·
              refine ⟨22466262022766457791377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1917121025942737731530837 22466262022766457791377)
              ·
                rfl

theorem cell21_885996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 8].length) (baseStart_885996 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_885996 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_885996 prefixEnd_885996 := by exact prefixLift 885996
  have htrace : WordTrace (prefixWord ++ tailWord_885996) baseStart_885996 baseEnd_885996 := by
    simpa [prefixWord, tailWord_885996, baseEnd_885996] using wordTrace_append hprefix tailTrace_885996
  have hstable : (prefixWord ++ tailWord_885996).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_885996).length < 2 ^ (prefixWord ++ tailWord_885996).sum := by decide
  have hdescent : baseEnd_885996 < baseStart_885996 := by decide
  rcases family_descends (prefixWord ++ tailWord_885996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_886027 : List Nat := [1, 1, 1, 1, 5, 3, 2, 2, 5]
def baseStart_886027 : Nat := 118140960795 + 886027 * 2 ^ 59
def prefixEnd_886027 : Nat := 4983230072969 + 3 ^ 40 * 886027 * 2
def baseEnd_886027 : Nat := 202203432827248955105663

theorem tailTrace_886027 : CollatzResearch.WordTrace tailWord_886027 prefixEnd_886027 202203432827248955105663 := by
  unfold tailWord_886027
  simp only [CollatzResearch.WordTrace]
  refine ⟨32316059561082975209400335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21544039707388650139600223 32316059561082975209400335)
  ·
    refine ⟨48474089341624462814100503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32316059561082975209400335 48474089341624462814100503)
    ·
      refine ⟨72711134012436694221150755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48474089341624462814100503 72711134012436694221150755)
      ·
        refine ⟨109066701018655041331726133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72711134012436694221150755 109066701018655041331726133)
        ·
          refine ⟨10225003220498910124849325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 109066701018655041331726133 10225003220498910124849325)
          ·
            refine ⟨3834376207687091296818497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10225003220498910124849325 3834376207687091296818497)
            ·
              refine ⟨2875782155765318472613873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3834376207687091296818497 2875782155765318472613873)
              ·
                refine ⟨2156836616823988854460405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2875782155765318472613873 2156836616823988854460405)
                ·
                  refine ⟨202203432827248955105663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2156836616823988854460405 202203432827248955105663)
                  ·
                    rfl

theorem cell21_886027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 2, 2, 5].length) (baseStart_886027 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_886027 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_886027 prefixEnd_886027 := by exact prefixLift 886027
  have htrace : WordTrace (prefixWord ++ tailWord_886027) baseStart_886027 baseEnd_886027 := by
    simpa [prefixWord, tailWord_886027, baseEnd_886027] using wordTrace_append hprefix tailTrace_886027
  have hstable : (prefixWord ++ tailWord_886027).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_886027).length < 2 ^ (prefixWord ++ tailWord_886027).sum := by decide
  have hdescent : baseEnd_886027 < baseStart_886027 := by decide
  rcases family_descends (prefixWord ++ tailWord_886027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_886030 : List Nat := [4, 1, 1, 2, 1, 5, 2, 5]
def baseStart_886030 : Nat := 118140960795 + 886030 * 2 ^ 59
def prefixEnd_886030 : Nat := 4983230072969 + 3 ^ 40 * 886030 * 2
def baseEnd_886030 : Nat := 67401372489373872185219

theorem tailTrace_886030 : CollatzResearch.WordTrace tailWord_886030 prefixEnd_886030 67401372489373872185219 := by
  unfold tailWord_886030
  simp only [CollatzResearch.WordTrace]
  refine ⟨4039521122509013340219943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21544112653381404481173029 4039521122509013340219943)
  ·
    refine ⟨6059281683763520010329915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4039521122509013340219943 6059281683763520010329915)
    ·
      refine ⟨9088922525645280015494873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6059281683763520010329915 9088922525645280015494873)
      ·
        refine ⟨6816691894233960011621155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9088922525645280015494873 6816691894233960011621155)
        ·
          refine ⟨10225037841350940017431733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6816691894233960011621155 10225037841350940017431733)
          ·
            refine ⟨958597297626650626634225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10225037841350940017431733 958597297626650626634225)
            ·
              refine ⟨718947973219987969975669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 958597297626650626634225 718947973219987969975669)
              ·
                refine ⟨67401372489373872185219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 718947973219987969975669 67401372489373872185219)
                ·
                  rfl

theorem cell21_886030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 2, 5].length) (baseStart_886030 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_886030 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_886030 prefixEnd_886030 := by exact prefixLift 886030
  have htrace : WordTrace (prefixWord ++ tailWord_886030) baseStart_886030 baseEnd_886030 := by
    simpa [prefixWord, tailWord_886030, baseEnd_886030] using wordTrace_append hprefix tailTrace_886030
  have hstable : (prefixWord ++ tailWord_886030).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_886030).length < 2 ^ (prefixWord ++ tailWord_886030).sum := by decide
  have hdescent : baseEnd_886030 < baseStart_886030 := by decide
  rcases family_descends (prefixWord ++ tailWord_886030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_886061 : List Nat := [1, 5, 3, 1, 1, 1, 3, 1, 5]
def baseStart_886061 : Nat := 118140960795 + 886061 * 2 ^ 59
def prefixEnd_886061 : Nat := 4983230072969 + 3 ^ 40 * 886061 * 2
def baseEnd_886061 : Nat := 202211192090472451538927

theorem tailTrace_886061 : CollatzResearch.WordTrace tailWord_886061 prefixEnd_886061 202211192090472451538927 := by
  unfold tailWord_886061
  simp only [CollatzResearch.WordTrace]
  refine ⟨32317299642959799016138037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21544866428639866010758691 32317299642959799016138037)
  ·
    refine ⟨3029746841527481157762941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 32317299642959799016138037 3029746841527481157762941)
    ·
      refine ⟨1136155065572805434161103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3029746841527481157762941 1136155065572805434161103)
      ·
        refine ⟨1704232598359208151241655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1136155065572805434161103 1704232598359208151241655)
        ·
          refine ⟨2556348897538812226862483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1704232598359208151241655 2556348897538812226862483)
          ·
            refine ⟨3834523346308218340293725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2556348897538812226862483 3834523346308218340293725)
            ·
              refine ⟨1437946254865581877610147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3834523346308218340293725 1437946254865581877610147)
              ·
                refine ⟨2156919382298372816415221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1437946254865581877610147 2156919382298372816415221)
                ·
                  refine ⟨202211192090472451538927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2156919382298372816415221 202211192090472451538927)
                  ·
                    rfl

theorem cell21_886061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 3, 1, 5].length) (baseStart_886061 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_886061 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_886061 prefixEnd_886061 := by exact prefixLift 886061
  have htrace : WordTrace (prefixWord ++ tailWord_886061) baseStart_886061 baseEnd_886061 := by
    simpa [prefixWord, tailWord_886061, baseEnd_886061] using wordTrace_append hprefix tailTrace_886061
  have hstable : (prefixWord ++ tailWord_886061).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_886061).length < 2 ^ (prefixWord ++ tailWord_886061).sum := by decide
  have hdescent : baseEnd_886061 < baseStart_886061 := by decide
  rcases family_descends (prefixWord ++ tailWord_886061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_886168 : List Nat := [2, 1, 2, 5, 2, 2, 1, 2, 4]
def baseStart_886168 : Nat := 118140960795 + 886168 * 2 ^ 59
def prefixEnd_886168 : Nat := 4983230072969 + 3 ^ 40 * 886168 * 2
def baseEnd_886168 : Nat := 202235610948264043255375

theorem tailTrace_886168 : CollatzResearch.WordTrace tailWord_886168 prefixEnd_886168 202235610948264043255375 := by
  unfold tailWord_886168
  simp only [CollatzResearch.WordTrace]
  refine ⟨16160601126786078145141579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21547468169048104193522105 16160601126786078145141579)
  ·
    refine ⟨24240901690179117217712369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16160601126786078145141579 24240901690179117217712369)
    ·
      refine ⟨18180676267634337913284277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24240901690179117217712369 18180676267634337913284277)
      ·
        refine ⟨1704438400090719179370401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 18180676267634337913284277 1704438400090719179370401)
        ·
          refine ⟨1278328800068039384527801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1704438400090719179370401 1278328800068039384527801)
          ·
            refine ⟨958746600051029538395851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1278328800068039384527801 958746600051029538395851)
            ·
              refine ⟨1438119900076544307593777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 958746600051029538395851 1438119900076544307593777)
              ·
                refine ⟨1078589925057408230695333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1438119900076544307593777 1078589925057408230695333)
                ·
                  refine ⟨202235610948264043255375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1078589925057408230695333 202235610948264043255375)
                  ·
                    rfl

theorem cell21_886168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 1, 2, 4].length) (baseStart_886168 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_886168 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_886168 prefixEnd_886168 := by exact prefixLift 886168
  have htrace : WordTrace (prefixWord ++ tailWord_886168) baseStart_886168 baseEnd_886168 := by
    simpa [prefixWord, tailWord_886168, baseEnd_886168] using wordTrace_append hprefix tailTrace_886168
  have hstable : (prefixWord ++ tailWord_886168).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_886168).length < 2 ^ (prefixWord ++ tailWord_886168).sum := by decide
  have hdescent : baseEnd_886168 < baseStart_886168 := by decide
  rcases family_descends (prefixWord ++ tailWord_886168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_886179 : List Nat := [1, 1, 1, 4, 1, 3, 4, 1, 5]
def baseStart_886179 : Nat := 118140960795 + 886179 * 2 ^ 59
def prefixEnd_886179 : Nat := 4983230072969 + 3 ^ 40 * 886179 * 2
def baseEnd_886179 : Nat := 202238121298130468572019

theorem tailTrace_886179 : CollatzResearch.WordTrace tailWord_886179 prefixEnd_886179 202238121298130468572019 := by
  unfold tailWord_886179
  simp only [CollatzResearch.WordTrace]
  refine ⟨32321603456532305168933591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21547735637688203445955727 32321603456532305168933591)
  ·
    refine ⟨48482405184798457753400387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32321603456532305168933591 48482405184798457753400387)
    ·
      refine ⟨72723607777197686630100581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48482405184798457753400387 72723607777197686630100581)
      ·
        refine ⟨13635676458224566243143859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72723607777197686630100581 13635676458224566243143859)
        ·
          refine ⟨20453514687336849364715789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13635676458224566243143859 20453514687336849364715789)
          ·
            refine ⟨7670068007751318511768421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20453514687336849364715789 7670068007751318511768421)
            ·
              refine ⟨1438137751453372220956579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7670068007751318511768421 1438137751453372220956579)
              ·
                refine ⟨2157206627180058331434869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1438137751453372220956579 2157206627180058331434869)
                ·
                  refine ⟨202238121298130468572019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2157206627180058331434869 202238121298130468572019)
                  ·
                    rfl

theorem cell21_886179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 4, 1, 5].length) (baseStart_886179 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_886179 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_886179 prefixEnd_886179 := by exact prefixLift 886179
  have htrace : WordTrace (prefixWord ++ tailWord_886179) baseStart_886179 baseEnd_886179 := by
    simpa [prefixWord, tailWord_886179, baseEnd_886179] using wordTrace_append hprefix tailTrace_886179
  have hstable : (prefixWord ++ tailWord_886179).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_886179).length < 2 ^ (prefixWord ++ tailWord_886179).sum := by decide
  have hdescent : baseEnd_886179 < baseStart_886179 := by decide
  rcases family_descends (prefixWord ++ tailWord_886179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_886278 : List Nat := [6, 2, 1, 1, 2, 1, 2, 2, 4]
def baseStart_886278 : Nat := 118140960795 + 886278 * 2 ^ 59
def prefixEnd_886278 : Nat := 4983230072969 + 3 ^ 40 * 886278 * 2
def baseEnd_886278 : Nat := 202260714446928296421817

theorem tailTrace_886278 : CollatzResearch.WordTrace tailWord_886278 prefixEnd_886278 202260714446928296421817 := by
  unfold tailWord_886278
  simp only [CollatzResearch.WordTrace]
  refine ⟨1010162946349176408649609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 21550142855449096717858325 1010162946349176408649609)
  ·
    refine ⟨757622209761882306487207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1010162946349176408649609 757622209761882306487207)
    ·
      refine ⟨1136433314642823459730811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 757622209761882306487207 1136433314642823459730811)
      ·
        refine ⟨1704649971964235189596217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1136433314642823459730811 1704649971964235189596217)
        ·
          refine ⟨1278487478973176392197163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1704649971964235189596217 1278487478973176392197163)
          ·
            refine ⟨1917731218459764588295745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1278487478973176392197163 1917731218459764588295745)
            ·
              refine ⟨1438298413844823441221809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1917731218459764588295745 1438298413844823441221809)
              ·
                refine ⟨1078723810383617580916357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1438298413844823441221809 1078723810383617580916357)
                ·
                  refine ⟨202260714446928296421817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1078723810383617580916357 202260714446928296421817)
                  ·
                    rfl

theorem cell21_886278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 2, 2, 4].length) (baseStart_886278 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_886278 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_886278 prefixEnd_886278 := by exact prefixLift 886278
  have htrace : WordTrace (prefixWord ++ tailWord_886278) baseStart_886278 baseEnd_886278 := by
    simpa [prefixWord, tailWord_886278, baseEnd_886278] using wordTrace_append hprefix tailTrace_886278
  have hstable : (prefixWord ++ tailWord_886278).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_886278).length < 2 ^ (prefixWord ++ tailWord_886278).sum := by decide
  have hdescent : baseEnd_886278 < baseStart_886278 := by decide
  rcases family_descends (prefixWord ++ tailWord_886278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_886283 : List Nat := [1, 1, 1, 1, 17]
def baseStart_886283 : Nat := 118140960795 + 886283 * 2 ^ 59
def prefixEnd_886283 : Nat := 4983230072969 + 3 ^ 40 * 886283 * 2
def baseEnd_886283 : Nat := 2497059944630239491833

theorem tailTrace_886283 : CollatzResearch.WordTrace tailWord_886283 prefixEnd_886283 2497059944630239491833 := by
  unfold tailWord_886283
  simp only [CollatzResearch.WordTrace]
  refine ⟨32325396648155530930719503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21550264432103687287146335 32325396648155530930719503)
  ·
    refine ⟨48488094972233296396079255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32325396648155530930719503 48488094972233296396079255)
    ·
      refine ⟨72732142458349944594118883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48488094972233296396079255 72732142458349944594118883)
      ·
        refine ⟨109098213687524916891178325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72732142458349944594118883 109098213687524916891178325)
        ·
          refine ⟨2497059944630239491833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 17 109098213687524916891178325 2497059944630239491833)
          ·
            rfl

theorem cell21_886283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 17].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 17].length) (baseStart_886283 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_886283 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_886283 prefixEnd_886283 := by exact prefixLift 886283
  have htrace : WordTrace (prefixWord ++ tailWord_886283) baseStart_886283 baseEnd_886283 := by
    simpa [prefixWord, tailWord_886283, baseEnd_886283] using wordTrace_append hprefix tailTrace_886283
  have hstable : (prefixWord ++ tailWord_886283).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_886283).length < 2 ^ (prefixWord ++ tailWord_886283).sum := by decide
  have hdescent : baseEnd_886283 < baseStart_886283 := by decide
  rcases family_descends (prefixWord ++ tailWord_886283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_886348 : List Nat := [2, 2, 1, 3, 1, 3, 2, 4, 3]
def baseStart_886348 : Nat := 118140960795 + 886348 * 2 ^ 59
def prefixEnd_886348 : Nat := 4983230072969 + 3 ^ 40 * 886348 * 2
def baseEnd_886348 : Nat := 202276689400623730255007

theorem tailTrace_886348 : CollatzResearch.WordTrace tailWord_886348 prefixEnd_886348 202276689400623730255007 := by
  unfold tailWord_886348
  simp only [CollatzResearch.WordTrace]
  refine ⟨16163883696460023515917849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21551844928613364687890465 16163883696460023515917849)
  ·
    refine ⟨12122912772345017636938387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16163883696460023515917849 12122912772345017636938387)
    ·
      refine ⟨18184369158517526455407581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12122912772345017636938387 18184369158517526455407581)
      ·
        refine ⟨6819138434444072420777843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18184369158517526455407581 6819138434444072420777843)
        ·
          refine ⟨10228707651666108631166765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6819138434444072420777843 10228707651666108631166765)
          ·
            refine ⟨3835765369374790736687537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10228707651666108631166765 3835765369374790736687537)
            ·
              refine ⟨2876824027031093052515653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3835765369374790736687537 2876824027031093052515653)
              ·
                refine ⟨539404505068329947346685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2876824027031093052515653 539404505068329947346685)
                ·
                  refine ⟨202276689400623730255007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 539404505068329947346685 202276689400623730255007)
                  ·
                    rfl

theorem cell21_886348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 2, 4, 3].length) (baseStart_886348 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_886348 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_886348 prefixEnd_886348 := by exact prefixLift 886348
  have htrace : WordTrace (prefixWord ++ tailWord_886348) baseStart_886348 baseEnd_886348 := by
    simpa [prefixWord, tailWord_886348, baseEnd_886348] using wordTrace_append hprefix tailTrace_886348
  have hstable : (prefixWord ++ tailWord_886348).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_886348).length < 2 ^ (prefixWord ++ tailWord_886348).sum := by decide
  have hdescent : baseEnd_886348 < baseStart_886348 := by decide
  rcases family_descends (prefixWord ++ tailWord_886348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_886382 : List Nat := [4, 1, 2, 2, 3, 2, 1, 3, 3]
def baseStart_886382 : Nat := 118140960795 + 886382 * 2 ^ 59
def prefixEnd_886382 : Nat := 4983230072969 + 3 ^ 40 * 886382 * 2
def baseEnd_886382 : Nat := 202284448663847226688271

theorem tailTrace_886382 : CollatzResearch.WordTrace tailWord_886382 prefixEnd_886382 202284448663847226688271 := by
  unfold tailWord_886382
  simp only [CollatzResearch.WordTrace]
  refine ⟨4041125934349608854821675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21552671649864580559048933 4041125934349608854821675)
  ·
    refine ⟨6061688901524413282232513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4041125934349608854821675 6061688901524413282232513)
    ·
      refine ⟨4546266676143309961674385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6061688901524413282232513 4546266676143309961674385)
      ·
        refine ⟨3409700007107482471255789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4546266676143309961674385 3409700007107482471255789)
        ·
          refine ⟨1278637502665305926720921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3409700007107482471255789 1278637502665305926720921)
          ·
            refine ⟨958978126998979445040691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1278637502665305926720921 958978126998979445040691)
            ·
              refine ⟨1438467190498469167561037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 958978126998979445040691 1438467190498469167561037)
              ·
                refine ⟨539425196436925937835389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1438467190498469167561037 539425196436925937835389)
                ·
                  refine ⟨202284448663847226688271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 539425196436925937835389 202284448663847226688271)
                  ·
                    rfl

theorem cell21_886382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 1, 3, 3].length) (baseStart_886382 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_886382 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_886382 prefixEnd_886382 := by exact prefixLift 886382
  have htrace : WordTrace (prefixWord ++ tailWord_886382) baseStart_886382 baseEnd_886382 := by
    simpa [prefixWord, tailWord_886382, baseEnd_886382] using wordTrace_append hprefix tailTrace_886382
  have hstable : (prefixWord ++ tailWord_886382).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_886382).length < 2 ^ (prefixWord ++ tailWord_886382).sum := by decide
  have hdescent : baseEnd_886382 < baseStart_886382 := by decide
  rcases family_descends (prefixWord ++ tailWord_886382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_886407 : List Nat := [1, 1, 4, 2, 1, 3, 3, 1, 5]
def baseStart_886407 : Nat := 118140960795 + 886407 * 2 ^ 59
def prefixEnd_886407 : Nat := 4983230072969 + 3 ^ 40 * 886407 * 2
def baseEnd_886407 : Nat := 202290154004452738771553

theorem tailTrace_886407 : CollatzResearch.WordTrace tailWord_886407 prefixEnd_886407 202290154004452738771553 := by
  unfold tailWord_886407
  simp only [CollatzResearch.WordTrace]
  refine ⟨32329919299706300108233475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21553279533137533405488983 32329919299706300108233475)
  ·
    refine ⟨48494878949559450162350213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32329919299706300108233475 48494878949559450162350213)
    ·
      refine ⟨9092789803042396905440665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48494878949559450162350213 9092789803042396905440665)
      ·
        refine ⟨6819592352281797679080499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9092789803042396905440665 6819592352281797679080499)
        ·
          refine ⟨10229388528422696518620749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6819592352281797679080499 10229388528422696518620749)
          ·
            refine ⟨3836020698158511194482781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10229388528422696518620749 3836020698158511194482781)
            ·
              refine ⟨1438507761809441697931043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3836020698158511194482781 1438507761809441697931043)
              ·
                refine ⟨2157761642714162546896565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1438507761809441697931043 2157761642714162546896565)
                ·
                  refine ⟨202290154004452738771553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2157761642714162546896565 202290154004452738771553)
                  ·
                    rfl

theorem cell21_886407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 3, 1, 5].length) (baseStart_886407 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_886407 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_886407 prefixEnd_886407 := by exact prefixLift 886407
  have htrace : WordTrace (prefixWord ++ tailWord_886407) baseStart_886407 baseEnd_886407 := by
    simpa [prefixWord, tailWord_886407, baseEnd_886407] using wordTrace_append hprefix tailTrace_886407
  have hstable : (prefixWord ++ tailWord_886407).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_886407).length < 2 ^ (prefixWord ++ tailWord_886407).sum := by decide
  have hdescent : baseEnd_886407 < baseStart_886407 := by decide
  rcases family_descends (prefixWord ++ tailWord_886407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_886435 : List Nat := [1, 1, 1, 4, 1, 1, 3, 9]
def baseStart_886435 : Nat := 118140960795 + 886435 * 2 ^ 59
def prefixEnd_886435 : Nat := 4983230072969 + 3 ^ 40 * 886435 * 2
def baseEnd_886435 : Nat := 67432181328643637434943

theorem tailTrace_886435 : CollatzResearch.WordTrace tailWord_886435 prefixEnd_886435 67432181328643637434943 := by
  unfold tailWord_886435
  simp only [CollatzResearch.WordTrace]
  refine ⟨32330940543604860890252759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21553960362403240593501839 32330940543604860890252759)
  ·
    refine ⟨48496410815407291335379139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32330940543604860890252759 48496410815407291335379139)
    ·
      refine ⟨72744616223110937003068709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48496410815407291335379139 72744616223110937003068709)
      ·
        refine ⟨13639615541833300688075383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72744616223110937003068709 13639615541833300688075383)
        ·
          refine ⟨20459423312749951032113075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13639615541833300688075383 20459423312749951032113075)
          ·
            refine ⟨30689134969124926548169613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20459423312749951032113075 30689134969124926548169613)
            ·
              refine ⟨11508425613421847455563605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30689134969124926548169613 11508425613421847455563605)
              ·
                refine ⟨67432181328643637434943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 11508425613421847455563605 67432181328643637434943)
                ·
                  rfl

theorem cell21_886435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 9].length) (baseStart_886435 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_886435 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_886435 prefixEnd_886435 := by exact prefixLift 886435
  have htrace : WordTrace (prefixWord ++ tailWord_886435) baseStart_886435 baseEnd_886435 := by
    simpa [prefixWord, tailWord_886435, baseEnd_886435] using wordTrace_append hprefix tailTrace_886435
  have hstable : (prefixWord ++ tailWord_886435).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_886435).length < 2 ^ (prefixWord ++ tailWord_886435).sum := by decide
  have hdescent : baseEnd_886435 < baseStart_886435 := by decide
  rcases family_descends (prefixWord ++ tailWord_886435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_886500 : List Nat := [2, 3, 1, 1, 1, 3, 4, 3, 3]
def baseStart_886500 : Nat := 118140960795 + 886500 * 2 ^ 59
def prefixEnd_886500 : Nat := 4983230072969 + 3 ^ 40 * 886500 * 2
def baseEnd_886500 : Nat := 202311377871505243721363

theorem tailTrace_886500 : CollatzResearch.WordTrace tailWord_886500 prefixEnd_886500 202311377871505243721363 := by
  unfold tailWord_886500
  simp only [CollatzResearch.WordTrace]
  refine ⟨16166655644184688495684477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21555540858912917994245969 16166655644184688495684477)
  ·
    refine ⟨6062495866569258185881679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16166655644184688495684477 6062495866569258185881679)
    ·
      refine ⟨9093743799853887278822519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6062495866569258185881679 9093743799853887278822519)
      ·
        refine ⟨13640615699780830918233779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9093743799853887278822519 13640615699780830918233779)
        ·
          refine ⟨20460923549671246377350669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13640615699780830918233779 20460923549671246377350669)
          ·
            refine ⟨7672846331126717391506501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20460923549671246377350669 7672846331126717391506501)
            ·
              refine ⟨1438658687086259510907469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7672846331126717391506501 1438658687086259510907469)
              ·
                refine ⟨539497007657347316590301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1438658687086259510907469 539497007657347316590301)
                ·
                  refine ⟨202311377871505243721363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 539497007657347316590301 202311377871505243721363)
                  ·
                    rfl

theorem cell21_886500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 4, 3, 3].length) (baseStart_886500 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_886500 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_886500 prefixEnd_886500 := by exact prefixLift 886500
  have htrace : WordTrace (prefixWord ++ tailWord_886500) baseStart_886500 baseEnd_886500 := by
    simpa [prefixWord, tailWord_886500, baseEnd_886500] using wordTrace_append hprefix tailTrace_886500
  have hstable : (prefixWord ++ tailWord_886500).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_886500).length < 2 ^ (prefixWord ++ tailWord_886500).sum := by decide
  have hdescent : baseEnd_886500 < baseStart_886500 := by decide
  rcases family_descends (prefixWord ++ tailWord_886500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_886511 : List Nat := [1, 1, 2, 1, 5, 1, 10]
def baseStart_886511 : Nat := 118140960795 + 886511 * 2 ^ 59
def prefixEnd_886511 : Nat := 4983230072969 + 3 ^ 40 * 886511 * 2
def baseEnd_886511 : Nat := 22479320913485741004223

theorem tailTrace_886511 : CollatzResearch.WordTrace tailWord_886511 prefixEnd_886511 22479320913485741004223 := by
  unfold tailWord_886511
  simp only [CollatzResearch.WordTrace]
  refine ⟨32333712491329525870019387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21555808327553017246679591 32333712491329525870019387)
  ·
    refine ⟨48500568736994288805029081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32333712491329525870019387 48500568736994288805029081)
    ·
      refine ⟨36375426552745716603771811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48500568736994288805029081 36375426552745716603771811)
      ·
        refine ⟨54563139829118574905657717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36375426552745716603771811 54563139829118574905657717)
        ·
          refine ⟨5115294358979866397405411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 54563139829118574905657717 5115294358979866397405411)
          ·
            refine ⟨7672941538469799596108117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5115294358979866397405411 7672941538469799596108117)
            ·
              refine ⟨22479320913485741004223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 7672941538469799596108117 22479320913485741004223)
              ·
                rfl

theorem cell21_886511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 10].length) (baseStart_886511 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_886511 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_886511 prefixEnd_886511 := by exact prefixLift 886511
  have htrace : WordTrace (prefixWord ++ tailWord_886511) baseStart_886511 baseEnd_886511 := by
    simpa [prefixWord, tailWord_886511, baseEnd_886511] using wordTrace_append hprefix tailTrace_886511
  have hstable : (prefixWord ++ tailWord_886511).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_886511).length < 2 ^ (prefixWord ++ tailWord_886511).sum := by decide
  have hdescent : baseEnd_886511 < baseStart_886511 := by decide
  rcases family_descends (prefixWord ++ tailWord_886511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_886649 : List Nat := [1, 2, 1, 3, 2, 2, 1, 5, 4]
def baseStart_886649 : Nat := 118140960795 + 886649 * 2 ^ 59
def prefixEnd_886649 : Nat := 4983230072969 + 3 ^ 40 * 886649 * 2
def baseEnd_886649 : Nat := 202345381701514095737725

theorem tailTrace_886649 : CollatzResearch.WordTrace tailWord_886649 prefixEnd_886649 202345381701514095737725 := by
  unfold tailWord_886649
  simp only [CollatzResearch.WordTrace]
  refine ⟨32338745764829575438543001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21559163843219716959028667 32338745764829575438543001)
  ·
    refine ⟨24254059323622181578907251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32338745764829575438543001 24254059323622181578907251)
    ·
      refine ⟨36381088985433272368360877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24254059323622181578907251 36381088985433272368360877)
      ·
        refine ⟨13642908369537477138135329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36381088985433272368360877 13642908369537477138135329)
        ·
          refine ⟨10232181277153107853601497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13642908369537477138135329 10232181277153107853601497)
          ·
            refine ⟨7674135957864830890201123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10232181277153107853601497 7674135957864830890201123)
            ·
              refine ⟨11511203936797246335301685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7674135957864830890201123 11511203936797246335301685)
              ·
                refine ⟨1079175369074741843934533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11511203936797246335301685 1079175369074741843934533)
                ·
                  refine ⟨202345381701514095737725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1079175369074741843934533 202345381701514095737725)
                  ·
                    rfl

theorem cell21_886649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 5, 4].length) (baseStart_886649 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_886649 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_886649 prefixEnd_886649 := by exact prefixLift 886649
  have htrace : WordTrace (prefixWord ++ tailWord_886649) baseStart_886649 baseEnd_886649 := by
    simpa [prefixWord, tailWord_886649, baseEnd_886649] using wordTrace_append hprefix tailTrace_886649
  have hstable : (prefixWord ++ tailWord_886649).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_886649).length < 2 ^ (prefixWord ++ tailWord_886649).sum := by decide
  have hdescent : baseEnd_886649 < baseStart_886649 := by decide
  rcases family_descends (prefixWord ++ tailWord_886649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_886728 : List Nat := [2, 1, 3, 1, 4, 1, 3, 3, 3]
def baseStart_886728 : Nat := 118140960795 + 886728 * 2 ^ 59
def prefixEnd_886728 : Nat := 4983230072969 + 3 ^ 40 * 886728 * 2
def baseEnd_886728 : Nat := 202363410577827513920897

theorem tailTrace_886728 : CollatzResearch.WordTrace tailWord_886728 prefixEnd_886728 202363410577827513920897 := by
  unfold tailWord_886728
  simp only [CollatzResearch.WordTrace]
  refine ⟨16170813565771685965334419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21561084754362247953779225 16170813565771685965334419)
  ·
    refine ⟨24256220348657528948001629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16170813565771685965334419 24256220348657528948001629)
    ·
      refine ⟨9096082630746573355500611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24256220348657528948001629 9096082630746573355500611)
      ·
        refine ⟨13644123946119860033250917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9096082630746573355500611 13644123946119860033250917)
        ·
          refine ⟨2558273239897473756234547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13644123946119860033250917 2558273239897473756234547)
          ·
            refine ⟨3837409859846210634351821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2558273239897473756234547 3837409859846210634351821)
            ·
              refine ⟨1439028697442328987881933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3837409859846210634351821 1439028697442328987881933)
              ·
                refine ⟨539635761540873370455725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1439028697442328987881933 539635761540873370455725)
                ·
                  refine ⟨202363410577827513920897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 539635761540873370455725 202363410577827513920897)
                  ·
                    rfl

theorem cell21_886728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 3, 3, 3].length) (baseStart_886728 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_886728 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_886728 prefixEnd_886728 := by exact prefixLift 886728
  have htrace : WordTrace (prefixWord ++ tailWord_886728) baseStart_886728 baseEnd_886728 := by
    simpa [prefixWord, tailWord_886728, baseEnd_886728] using wordTrace_append hprefix tailTrace_886728
  have hstable : (prefixWord ++ tailWord_886728).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_886728).length < 2 ^ (prefixWord ++ tailWord_886728).sum := by decide
  have hdescent : baseEnd_886728 < baseStart_886728 := by decide
  rcases family_descends (prefixWord ++ tailWord_886728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_886745 : List Nat := [1, 2, 1, 2, 6, 1, 3, 2, 3]
def baseStart_886745 : Nat := 118140960795 + 886745 * 2 ^ 59
def prefixEnd_886745 : Nat := 4983230072969 + 3 ^ 40 * 886745 * 2
def baseEnd_886745 : Nat := 202367290209439262137529

theorem tailTrace_886745 : CollatzResearch.WordTrace tailWord_886745 prefixEnd_886745 202367290209439262137529 := by
  unfold tailWord_886745
  simp only [CollatzResearch.WordTrace]
  refine ⟨32342247172481783834037689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21561498114987855889358459 32342247172481783834037689)
  ·
    refine ⟨24256685379361337875528267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32342247172481783834037689 24256685379361337875528267)
    ·
      refine ⟨36385028069042006813292401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24256685379361337875528267 36385028069042006813292401)
      ·
        refine ⟨27288771051781505109969301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36385028069042006813292401 27288771051781505109969301)
        ·
          refine ⟨1279161143052258052029811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 27288771051781505109969301 1279161143052258052029811)
          ·
            refine ⟨1918741714578387078044717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1279161143052258052029811 1918741714578387078044717)
            ·
              refine ⟨719528142966895154266769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1918741714578387078044717 719528142966895154266769)
              ·
                refine ⟨539646107225171365700077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 719528142966895154266769 539646107225171365700077)
                ·
                  refine ⟨202367290209439262137529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 539646107225171365700077 202367290209439262137529)
                  ·
                    rfl

theorem cell21_886745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 3, 2, 3].length) (baseStart_886745 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_886745 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_886745 prefixEnd_886745 := by exact prefixLift 886745
  have htrace : WordTrace (prefixWord ++ tailWord_886745) baseStart_886745 baseEnd_886745 := by
    simpa [prefixWord, tailWord_886745, baseEnd_886745] using wordTrace_append hprefix tailTrace_886745
  have hstable : (prefixWord ++ tailWord_886745).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_886745).length < 2 ^ (prefixWord ++ tailWord_886745).sum := by decide
  have hdescent : baseEnd_886745 < baseStart_886745 := by decide
  rcases family_descends (prefixWord ++ tailWord_886745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_886784 : List Nat := [2, 1, 1, 2, 1, 1, 1, 6, 6]
def baseStart_886784 : Nat := 118140960795 + 886784 * 2 ^ 59
def prefixEnd_886784 : Nat := 4983230072969 + 3 ^ 40 * 886784 * 2
def baseEnd_886784 : Nat := 202376190540783860987449

theorem tailTrace_886784 : CollatzResearch.WordTrace tailWord_886784 prefixEnd_886784 202376190540783860987449 := by
  unfold tailWord_886784
  simp only [CollatzResearch.WordTrace]
  refine ⟨16171834809670246747353703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21562446412893662329804937 16171834809670246747353703)
  ·
    refine ⟨24257752214505370121030555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16171834809670246747353703 24257752214505370121030555)
    ·
      refine ⟨36386628321758055181545833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24257752214505370121030555 36386628321758055181545833)
      ·
        refine ⟨27289971241318541386159375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36386628321758055181545833 27289971241318541386159375)
        ·
          refine ⟨40934956861977812079239063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27289971241318541386159375 40934956861977812079239063)
          ·
            refine ⟨61402435292966718118858595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40934956861977812079239063 61402435292966718118858595)
            ·
              refine ⟨92103652939450077178287893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61402435292966718118858595 92103652939450077178287893)
              ·
                refine ⟨4317358731536722367732245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 92103652939450077178287893 4317358731536722367732245)
                ·
                  refine ⟨202376190540783860987449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4317358731536722367732245 202376190540783860987449)
                  ·
                    rfl

theorem cell21_886784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 6, 6].length) (baseStart_886784 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_886784 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_886784 prefixEnd_886784 := by exact prefixLift 886784
  have htrace : WordTrace (prefixWord ++ tailWord_886784) baseStart_886784 baseEnd_886784 := by
    simpa [prefixWord, tailWord_886784, baseEnd_886784] using wordTrace_append hprefix tailTrace_886784
  have hstable : (prefixWord ++ tailWord_886784).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_886784).length < 2 ^ (prefixWord ++ tailWord_886784).sum := by decide
  have hdescent : baseEnd_886784 < baseStart_886784 := by decide
  rcases family_descends (prefixWord ++ tailWord_886784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_886790 : List Nat := [6, 2, 1, 2, 10]
def baseStart_886790 : Nat := 118140960795 + 886790 * 2 ^ 59
def prefixEnd_886790 : Nat := 4983230072969 + 3 ^ 40 * 886790 * 2
def baseEnd_886790 : Nat := 2498488392870730665277

theorem tailTrace_886790 : CollatzResearch.WordTrace tailWord_886790 prefixEnd_886790 2498488392870730665277 := by
  unfold tailWord_886790
  simp only [CollatzResearch.WordTrace]
  refine ⟨1010746514291211141232057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 21562592304879171012950549 1010746514291211141232057)
  ·
    refine ⟨758059885718408355924043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1010746514291211141232057 758059885718408355924043)
    ·
      refine ⟨1137089828577612533886065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 758059885718408355924043 1137089828577612533886065)
      ·
        refine ⟨852817371433209400414549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1137089828577612533886065 852817371433209400414549)
        ·
          refine ⟨2498488392870730665277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 852817371433209400414549 2498488392870730665277)
          ·
            rfl

theorem cell21_886790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 10].length) (baseStart_886790 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_886790 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_886790 prefixEnd_886790 := by exact prefixLift 886790
  have htrace : WordTrace (prefixWord ++ tailWord_886790) baseStart_886790 baseEnd_886790 := by
    simpa [prefixWord, tailWord_886790, baseEnd_886790] using wordTrace_append hprefix tailTrace_886790
  have hstable : (prefixWord ++ tailWord_886790).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_886790).length < 2 ^ (prefixWord ++ tailWord_886790).sum := by decide
  have hdescent : baseEnd_886790 < baseStart_886790 := by decide
  rcases family_descends (prefixWord ++ tailWord_886790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_886832 : List Nat := [2, 1, 1, 1, 2, 6, 3, 5]
def baseStart_886832 : Nat := 118140960795 + 886832 * 2 ^ 59
def prefixEnd_886832 : Nat := 4983230072969 + 3 ^ 40 * 886832 * 2
def baseEnd_886832 : Nat := 67462381598248814729117

theorem tailTrace_886832 : CollatzResearch.WordTrace tailWord_886832 prefixEnd_886832 67462381598248814729117 := by
  unfold tailWord_886832
  simp only [CollatzResearch.WordTrace]
  refine ⟨16172710161583298846227375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21563613548777731794969833 16172710161583298846227375)
  ·
    refine ⟨24259065242374948269341063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16172710161583298846227375 24259065242374948269341063)
    ·
      refine ⟨36388597863562422404011595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24259065242374948269341063 36388597863562422404011595)
      ·
        refine ⟨54582896795343633606017393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36388597863562422404011595 54582896795343633606017393)
        ·
          refine ⟨40937172596507725204513045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54582896795343633606017393 40937172596507725204513045)
          ·
            refine ⟨1918929965461299618961549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 40937172596507725204513045 1918929965461299618961549)
            ·
              refine ⟨719598737047987357110581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1918929965461299618961549 719598737047987357110581)
              ·
                refine ⟨67462381598248814729117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 719598737047987357110581 67462381598248814729117)
                ·
                  rfl

theorem cell21_886832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 3, 5].length) (baseStart_886832 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_886832 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_886832 prefixEnd_886832 := by exact prefixLift 886832
  have htrace : WordTrace (prefixWord ++ tailWord_886832) baseStart_886832 baseEnd_886832 := by
    simpa [prefixWord, tailWord_886832, baseEnd_886832] using wordTrace_append hprefix tailTrace_886832
  have hstable : (prefixWord ++ tailWord_886832).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_886832).length < 2 ^ (prefixWord ++ tailWord_886832).sum := by decide
  have hdescent : baseEnd_886832 < baseStart_886832 := by decide
  rcases family_descends (prefixWord ++ tailWord_886832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_887012 : List Nat := [2, 3, 1, 1, 1, 2, 1, 4, 6]
def baseStart_887012 : Nat := 118140960795 + 887012 * 2 ^ 59
def prefixEnd_887012 : Nat := 4983230072969 + 3 ^ 40 * 887012 * 2
def baseEnd_887012 : Nat := 202428223247106131186983

theorem tailTrace_887012 : CollatzResearch.WordTrace tailWord_887012 prefixEnd_887012 202428223247106131186983 := by
  unfold tailWord_887012
  simp only [CollatzResearch.WordTrace]
  refine ⟨16175992731257244217003645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21567990308342992289338193 16175992731257244217003645)
  ·
    refine ⟨6065997274221466581376367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16175992731257244217003645 6065997274221466581376367)
    ·
      refine ⟨9098995911332199872064551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6065997274221466581376367 9098995911332199872064551)
      ·
        refine ⟨13648493866998299808096827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9098995911332199872064551 13648493866998299808096827)
        ·
          refine ⟨20472740800497449712145241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13648493866998299808096827 20472740800497449712145241)
          ·
            refine ⟨15354555600373087284108931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20472740800497449712145241 15354555600373087284108931)
            ·
              refine ⟨23031833400559630926163397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15354555600373087284108931 23031833400559630926163397)
              ·
                refine ⟨4318468762604930798655637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23031833400559630926163397 4318468762604930798655637)
                ·
                  refine ⟨202428223247106131186983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4318468762604930798655637 202428223247106131186983)
                  ·
                    rfl

theorem cell21_887012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 4, 6].length) (baseStart_887012 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_887012 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_887012 prefixEnd_887012 := by exact prefixLift 887012
  have htrace : WordTrace (prefixWord ++ tailWord_887012) baseStart_887012 baseEnd_887012 := by
    simpa [prefixWord, tailWord_887012, baseEnd_887012] using wordTrace_append hprefix tailTrace_887012
  have hstable : (prefixWord ++ tailWord_887012).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_887012).length < 2 ^ (prefixWord ++ tailWord_887012).sum := by decide
  have hdescent : baseEnd_887012 < baseStart_887012 := by decide
  rcases family_descends (prefixWord ++ tailWord_887012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_887170 : List Nat := [3, 4, 2, 1, 2, 1, 3, 5]
def baseStart_887170 : Nat := 118140960795 + 887170 * 2 ^ 59
def prefixEnd_887170 : Nat := 4983230072969 + 3 ^ 40 * 887170 * 2
def baseEnd_887170 : Nat := 67488093666577655851109

theorem tailTrace_887170 : CollatzResearch.WordTrace tailWord_887170 prefixEnd_887170 67488093666577655851109 := by
  unfold tailWord_887170
  simp only [CollatzResearch.WordTrace]
  refine ⟨8089437048985520354564741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21571832130628054278839309 8089437048985520354564741)
  ·
    refine ⟨1516769446684785066480889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8089437048985520354564741 1516769446684785066480889)
    ·
      refine ⟨1137577085013588799860667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1516769446684785066480889 1137577085013588799860667)
      ·
        refine ⟨1706365627520383199791001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1137577085013588799860667 1706365627520383199791001)
        ·
          refine ⟨1279774220640287399843251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1706365627520383199791001 1279774220640287399843251)
          ·
            refine ⟨1919661330960431099764877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1279774220640287399843251 1919661330960431099764877)
            ·
              refine ⟨719872999110161662411829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1919661330960431099764877 719872999110161662411829)
              ·
                refine ⟨67488093666577655851109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 719872999110161662411829 67488093666577655851109)
                ·
                  rfl

theorem cell21_887170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 3, 5].length) (baseStart_887170 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_887170 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_887170 prefixEnd_887170 := by exact prefixLift 887170
  have htrace : WordTrace (prefixWord ++ tailWord_887170) baseStart_887170 baseEnd_887170 := by
    simpa [prefixWord, tailWord_887170, baseEnd_887170] using wordTrace_append hprefix tailTrace_887170
  have hstable : (prefixWord ++ tailWord_887170).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_887170).length < 2 ^ (prefixWord ++ tailWord_887170).sum := by decide
  have hdescent : baseEnd_887170 < baseStart_887170 := by decide
  rcases family_descends (prefixWord ++ tailWord_887170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_887190 : List Nat := [5, 3, 1, 2, 2, 1, 1, 2, 4]
def baseStart_887190 : Nat := 118140960795 + 887190 * 2 ^ 59
def prefixEnd_887190 : Nat := 4983230072969 + 3 ^ 40 * 887190 * 2
def baseEnd_887190 : Nat := 202468845272217377219953

theorem tailTrace_887190 : CollatzResearch.WordTrace tailWord_887190 prefixEnd_887190 202468845272217377219953 := by
  unfold tailWord_887190
  simp only [CollatzResearch.WordTrace]
  refine ⟨2022404853491851552124189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21572318437246416555991349 2022404853491851552124189)
  ·
    refine ⟨758401820059444332046571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2022404853491851552124189 758401820059444332046571)
    ·
      refine ⟨1137602730089166498069857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 758401820059444332046571 1137602730089166498069857)
      ·
        refine ⟨853202047566874873552393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1137602730089166498069857 853202047566874873552393)
        ·
          refine ⟨639901535675156155164295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 853202047566874873552393 639901535675156155164295)
          ·
            refine ⟨959852303512734232746443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 639901535675156155164295 959852303512734232746443)
            ·
              refine ⟨1439778455269101349119665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 959852303512734232746443 1439778455269101349119665)
              ·
                refine ⟨1079833841451826011839749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1439778455269101349119665 1079833841451826011839749)
                ·
                  refine ⟨202468845272217377219953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1079833841451826011839749 202468845272217377219953)
                  ·
                    rfl

theorem cell21_887190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 1, 2, 4].length) (baseStart_887190 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_887190 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_887190 prefixEnd_887190 := by exact prefixLift 887190
  have htrace : WordTrace (prefixWord ++ tailWord_887190) baseStart_887190 baseEnd_887190 := by
    simpa [prefixWord, tailWord_887190, baseEnd_887190] using wordTrace_append hprefix tailTrace_887190
  have hstable : (prefixWord ++ tailWord_887190).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_887190).length < 2 ^ (prefixWord ++ tailWord_887190).sum := by decide
  have hdescent : baseEnd_887190 < baseStart_887190 := by decide
  rcases family_descends (prefixWord ++ tailWord_887190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_887198 : List Nat := [4, 3, 1, 2, 1, 2, 1, 1, 6]
def baseStart_887198 : Nat := 118140960795 + 887198 * 2 ^ 59
def prefixEnd_887198 : Nat := 4983230072969 + 3 ^ 40 * 887198 * 2
def baseEnd_887198 : Nat := 202470670981211141086603

theorem tailTrace_887198 : CollatzResearch.WordTrace tailWord_887198 prefixEnd_887198 202470670981211141086603 := by
  unfold tailWord_887198
  simp only [CollatzResearch.WordTrace]
  refine ⟨4044846179980080275034781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21572512959893761466852165 4044846179980080275034781)
  ·
    refine ⟨1516817317492530103138043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4044846179980080275034781 1516817317492530103138043)
    ·
      refine ⟨2275225976238795154707065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1516817317492530103138043 2275225976238795154707065)
      ·
        refine ⟨1706419482179096366030299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2275225976238795154707065 1706419482179096366030299)
        ·
          refine ⟨2559629223268644549045449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1706419482179096366030299 2559629223268644549045449)
          ·
            refine ⟨1919721917451483411784087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2559629223268644549045449 1919721917451483411784087)
            ·
              refine ⟨2879582876177225117676131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1919721917451483411784087 2879582876177225117676131)
              ·
                refine ⟨4319374314265837676514197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2879582876177225117676131 4319374314265837676514197)
                ·
                  refine ⟨202470670981211141086603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4319374314265837676514197 202470670981211141086603)
                  ·
                    rfl

theorem cell21_887198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 1, 1, 6].length) (baseStart_887198 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_887198 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_887198 prefixEnd_887198 := by exact prefixLift 887198
  have htrace : WordTrace (prefixWord ++ tailWord_887198) baseStart_887198 baseEnd_887198 := by
    simpa [prefixWord, tailWord_887198, baseEnd_887198] using wordTrace_append hprefix tailTrace_887198
  have hstable : (prefixWord ++ tailWord_887198).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_887198).length < 2 ^ (prefixWord ++ tailWord_887198).sum := by decide
  have hdescent : baseEnd_887198 < baseStart_887198 := by decide
  rcases family_descends (prefixWord ++ tailWord_887198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_887240 : List Nat := [2, 1, 3, 1, 3, 2, 1, 2, 6]
def baseStart_887240 : Nat := 118140960795 + 887240 * 2 ^ 59
def prefixEnd_887240 : Nat := 4983230072969 + 3 ^ 40 * 887240 * 2
def baseEnd_887240 : Nat := 202480255953428401386517

theorem tailTrace_887240 : CollatzResearch.WordTrace tailWord_887240 prefixEnd_887240 202480255953428401386517 := by
  unfold tailWord_887240
  simp only [CollatzResearch.WordTrace]
  refine ⟨16180150652844241686653587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21573534203792322248871449 16180150652844241686653587)
  ·
    refine ⟨24270225979266362529980381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16180150652844241686653587 24270225979266362529980381)
    ·
      refine ⟨9101334742224885948742643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24270225979266362529980381 9101334742224885948742643)
      ·
        refine ⟨13652002113337328923113965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9101334742224885948742643 13652002113337328923113965)
        ·
          refine ⟨5119500792501498346167737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13652002113337328923113965 5119500792501498346167737)
          ·
            refine ⟨3839625594376123759625803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5119500792501498346167737 3839625594376123759625803)
            ·
              refine ⟨5759438391564185639438705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3839625594376123759625803 5759438391564185639438705)
              ·
                refine ⟨4319578793673139229579029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5759438391564185639438705 4319578793673139229579029)
                ·
                  refine ⟨202480255953428401386517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4319578793673139229579029 202480255953428401386517)
                  ·
                    rfl

theorem cell21_887240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 2, 6].length) (baseStart_887240 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_887240 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_887240 prefixEnd_887240 := by exact prefixLift 887240
  have htrace : WordTrace (prefixWord ++ tailWord_887240) baseStart_887240 baseEnd_887240 := by
    simpa [prefixWord, tailWord_887240, baseEnd_887240] using wordTrace_append hprefix tailTrace_887240
  have hstable : (prefixWord ++ tailWord_887240).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_887240).length < 2 ^ (prefixWord ++ tailWord_887240).sum := by decide
  have hdescent : baseEnd_887240 < baseStart_887240 := by decide
  rcases family_descends (prefixWord ++ tailWord_887240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_887271 : List Nat := [1, 1, 5, 2, 1, 1, 4, 6]
def baseStart_887271 : Nat := 118140960795 + 887271 * 2 ^ 59
def prefixEnd_887271 : Nat := 4983230072969 + 3 ^ 40 * 887271 * 2
def baseEnd_887271 : Nat := 67495776858593078789929

theorem tailTrace_887271 : CollatzResearch.WordTrace tailWord_887271 prefixEnd_887271 67495776858593078789929 := by
  unfold tailWord_887271
  simp only [CollatzResearch.WordTrace]
  refine ⟨32361431968576175667685667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21574287979050783778457111 32361431968576175667685667)
  ·
    refine ⟨48542147952864263501528501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32361431968576175667685667 48542147952864263501528501)
    ·
      refine ⟨4550826370581024703268297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 48542147952864263501528501 4550826370581024703268297)
      ·
        refine ⟨3413119777935768527451223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4550826370581024703268297 3413119777935768527451223)
        ·
          refine ⟨5119679666903652791176835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3413119777935768527451223 5119679666903652791176835)
          ·
            refine ⟨7679519500355479186765253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5119679666903652791176835 7679519500355479186765253)
            ·
              refine ⟨1439909906316652347518485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7679519500355479186765253 1439909906316652347518485)
              ·
                refine ⟨67495776858593078789929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1439909906316652347518485 67495776858593078789929)
                ·
                  rfl

theorem cell21_887271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 4, 6].length) (baseStart_887271 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_887271 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_887271 prefixEnd_887271 := by exact prefixLift 887271
  have htrace : WordTrace (prefixWord ++ tailWord_887271) baseStart_887271 baseEnd_887271 := by
    simpa [prefixWord, tailWord_887271, baseEnd_887271] using wordTrace_append hprefix tailTrace_887271
  have hstable : (prefixWord ++ tailWord_887271).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_887271).length < 2 ^ (prefixWord ++ tailWord_887271).sum := by decide
  have hdescent : baseEnd_887271 < baseStart_887271 := by decide
  rcases family_descends (prefixWord ++ tailWord_887271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_887274 : List Nat := [3, 1, 3, 1, 3, 1, 4, 1, 4]
def baseStart_887274 : Nat := 118140960795 + 887274 * 2 ^ 59
def prefixEnd_887274 : Nat := 4983230072969 + 3 ^ 40 * 887274 * 2
def baseEnd_887274 : Nat := 202488015216651897819781

theorem tailTrace_887274 : CollatzResearch.WordTrace tailWord_887274 prefixEnd_887274 202488015216651897819781 := by
  unfold tailWord_887274
  simp only [CollatzResearch.WordTrace]
  refine ⟨8090385346891326795011219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21574360925043538120029917 8090385346891326795011219)
  ·
    refine ⟨12135578020336990192516829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8090385346891326795011219 12135578020336990192516829)
    ·
      refine ⟨4550841757626371322193811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12135578020336990192516829 4550841757626371322193811)
      ·
        refine ⟨6826262636439556983290717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4550841757626371322193811 6826262636439556983290717)
        ·
          refine ⟨2559848488664833868734019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6826262636439556983290717 2559848488664833868734019)
          ·
            refine ⟨3839772732997250803101029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2559848488664833868734019 3839772732997250803101029)
            ·
              refine ⟨719957387436984525581443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3839772732997250803101029 719957387436984525581443)
              ·
                refine ⟨1079936081155476788372165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 719957387436984525581443 1079936081155476788372165)
                ·
                  refine ⟨202488015216651897819781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1079936081155476788372165 202488015216651897819781)
                  ·
                    rfl

theorem cell21_887274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 4, 1, 4].length) (baseStart_887274 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_887274 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_887274 prefixEnd_887274 := by exact prefixLift 887274
  have htrace : WordTrace (prefixWord ++ tailWord_887274) baseStart_887274 baseEnd_887274 := by
    simpa [prefixWord, tailWord_887274, baseEnd_887274] using wordTrace_append hprefix tailTrace_887274
  have hstable : (prefixWord ++ tailWord_887274).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_887274).length < 2 ^ (prefixWord ++ tailWord_887274).sum := by decide
  have hdescent : baseEnd_887274 < baseStart_887274 := by decide
  rcases family_descends (prefixWord ++ tailWord_887274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_887347 : List Nat := [1, 1, 1, 2, 4, 2, 5, 5]
def baseStart_887347 : Nat := 118140960795 + 887347 * 2 ^ 59
def prefixEnd_887347 : Nat := 4983230072969 + 3 ^ 40 * 887347 * 2
def baseEnd_887347 : Nat := 67501558270406664367655

theorem tailTrace_887347 : CollatzResearch.WordTrace tailWord_887347 prefixEnd_887347 67501558270406664367655 := by
  unfold tailWord_887347
  simp only [CollatzResearch.WordTrace]
  refine ⟨32364203916300840647452295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21576135944200560431634863 32364203916300840647452295)
  ·
    refine ⟨48546305874451260971178443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32364203916300840647452295 48546305874451260971178443)
    ·
      refine ⟨72819458811676891456767665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48546305874451260971178443 72819458811676891456767665)
      ·
        refine ⟨54614594108757668592575749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72819458811676891456767665 54614594108757668592575749)
        ·
          refine ⟨10240236395392062861107953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54614594108757668592575749 10240236395392062861107953)
          ·
            refine ⟨7680177296544047145830965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10240236395392062861107953 7680177296544047145830965)
            ·
              refine ⟨720016621551004419921653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7680177296544047145830965 720016621551004419921653)
              ·
                refine ⟨67501558270406664367655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 720016621551004419921653 67501558270406664367655)
                ·
                  rfl

theorem cell21_887347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 5, 5].length) (baseStart_887347 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_887347 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_887347 prefixEnd_887347 := by exact prefixLift 887347
  have htrace : WordTrace (prefixWord ++ tailWord_887347) baseStart_887347 baseEnd_887347 := by
    simpa [prefixWord, tailWord_887347, baseEnd_887347] using wordTrace_append hprefix tailTrace_887347
  have hstable : (prefixWord ++ tailWord_887347).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_887347).length < 2 ^ (prefixWord ++ tailWord_887347).sum := by decide
  have hdescent : baseEnd_887347 < baseStart_887347 := by decide
  rcases family_descends (prefixWord ++ tailWord_887347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_887378 : List Nat := [3, 2, 2, 1, 2, 1, 4, 1, 5]
def baseStart_887378 : Nat := 118140960795 + 887378 * 2 ^ 59
def prefixEnd_887378 : Nat := 4983230072969 + 3 ^ 40 * 887378 * 2
def baseEnd_887378 : Nat := 202511749433570828086235

theorem tailTrace_887378 : CollatzResearch.WordTrace tailWord_887378 prefixEnd_887378 202511749433570828086235 := by
  unfold tailWord_887378
  simp only [CollatzResearch.WordTrace]
  refine ⟨8091333644797133235457697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21576889719459021961220525 8091333644797133235457697)
  ·
    refine ⟨6068500233597849926593273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8091333644797133235457697 6068500233597849926593273)
    ·
      refine ⟨4551375175198387444944955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6068500233597849926593273 4551375175198387444944955)
      ·
        refine ⟨6827062762797581167417433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4551375175198387444944955 6827062762797581167417433)
        ·
          refine ⟨5120297072098185875563075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6827062762797581167417433 5120297072098185875563075)
          ·
            refine ⟨7680445608147278813344613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5120297072098185875563075 7680445608147278813344613)
            ·
              refine ⟨1440083551527614777502115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7680445608147278813344613 1440083551527614777502115)
              ·
                refine ⟨2160125327291422166253173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1440083551527614777502115 2160125327291422166253173)
                ·
                  refine ⟨202511749433570828086235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2160125327291422166253173 202511749433570828086235)
                  ·
                    rfl

theorem cell21_887378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 4, 1, 5].length) (baseStart_887378 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_887378 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_887378 prefixEnd_887378 := by exact prefixLift 887378
  have htrace : WordTrace (prefixWord ++ tailWord_887378) baseStart_887378 baseEnd_887378 := by
    simpa [prefixWord, tailWord_887378, baseEnd_887378] using wordTrace_append hprefix tailTrace_887378
  have hstable : (prefixWord ++ tailWord_887378).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_887378).length < 2 ^ (prefixWord ++ tailWord_887378).sum := by decide
  have hdescent : baseEnd_887378 < baseStart_887378 := by decide
  rcases family_descends (prefixWord ++ tailWord_887378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_887392 : List Nat := [2, 1, 1, 3, 2, 1, 2, 5, 4]
def baseStart_887392 : Nat := 118140960795 + 887392 * 2 ^ 59
def prefixEnd_887392 : Nat := 4983230072969 + 3 ^ 40 * 887392 * 2
def baseEnd_887392 : Nat := 202514944424309914852873

theorem tailTrace_887392 : CollatzResearch.WordTrace tailWord_887392 prefixEnd_887392 202514944424309914852873 := by
  unfold tailWord_887392
  simp only [CollatzResearch.WordTrace]
  refine ⟨16182922600568906666420215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21577230134091875555226953 16182922600568906666420215)
  ·
    refine ⟨24274383900853359999630323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16182922600568906666420215 24274383900853359999630323)
    ·
      refine ⟨36411575851280039999445485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24274383900853359999630323 36411575851280039999445485)
      ·
        refine ⟨13654340944230014999792057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36411575851280039999445485 13654340944230014999792057)
        ·
          refine ⟨10240755708172511249844043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13654340944230014999792057 10240755708172511249844043)
          ·
            refine ⟨15361133562258766874766065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10240755708172511249844043 15361133562258766874766065)
            ·
              refine ⟨11520850171694075156074549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15361133562258766874766065 11520850171694075156074549)
              ·
                refine ⟨1080079703596319545881989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11520850171694075156074549 1080079703596319545881989)
                ·
                  refine ⟨202514944424309914852873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1080079703596319545881989 202514944424309914852873)
                  ·
                    rfl

theorem cell21_887392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 5, 4].length) (baseStart_887392 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_887392 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_887392 prefixEnd_887392 := by exact prefixLift 887392
  have htrace : WordTrace (prefixWord ++ tailWord_887392) baseStart_887392 baseEnd_887392 := by
    simpa [prefixWord, tailWord_887392, baseEnd_887392] using wordTrace_append hprefix tailTrace_887392
  have hstable : (prefixWord ++ tailWord_887392).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_887392).length < 2 ^ (prefixWord ++ tailWord_887392).sum := by decide
  have hdescent : baseEnd_887392 < baseStart_887392 := by decide
  rcases family_descends (prefixWord ++ tailWord_887392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_887454 : List Nat := [4, 3, 1, 1, 1, 1, 2, 1, 7]
def baseStart_887454 : Nat := 118140960795 + 887454 * 2 ^ 59
def prefixEnd_887454 : Nat := 4983230072969 + 3 ^ 40 * 887454 * 2
def baseEnd_887454 : Nat := 202529093669011584819413

theorem tailTrace_887454 : CollatzResearch.WordTrace tailWord_887454 prefixEnd_887454 202529093669011584819413 := by
  unfold tailWord_887454
  simp only [CollatzResearch.WordTrace]
  refine ⟨4046013315864149740199677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21578737684608798614398277 4046013315864149740199677)
  ·
    refine ⟨1517254993449056152574879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4046013315864149740199677 1517254993449056152574879)
    ·
      refine ⟨2275882490173584228862319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1517254993449056152574879 2275882490173584228862319)
      ·
        refine ⟨3413823735260376343293479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2275882490173584228862319 3413823735260376343293479)
        ·
          refine ⟨5120735602890564514940219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3413823735260376343293479 5120735602890564514940219)
          ·
            refine ⟨7681103404335846772410329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5120735602890564514940219 7681103404335846772410329)
            ·
              refine ⟨5760827553251885079307747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7681103404335846772410329 5760827553251885079307747)
              ·
                refine ⟨8641241329877827618961621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5760827553251885079307747 8641241329877827618961621)
                ·
                  refine ⟨202529093669011584819413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8641241329877827618961621 202529093669011584819413)
                  ·
                    rfl

theorem cell21_887454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 1, 7].length) (baseStart_887454 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_887454 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_887454 prefixEnd_887454 := by exact prefixLift 887454
  have htrace : WordTrace (prefixWord ++ tailWord_887454) baseStart_887454 baseEnd_887454 := by
    simpa [prefixWord, tailWord_887454, baseEnd_887454] using wordTrace_append hprefix tailTrace_887454
  have hstable : (prefixWord ++ tailWord_887454).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_887454).length < 2 ^ (prefixWord ++ tailWord_887454).sum := by decide
  have hdescent : baseEnd_887454 < baseStart_887454 := by decide
  rcases family_descends (prefixWord ++ tailWord_887454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_887485 : List Nat := [1, 4, 1, 2, 1, 4, 2, 2, 4]
def baseStart_887485 : Nat := 118140960795 + 887485 * 2 ^ 59
def prefixEnd_887485 : Nat := 4983230072969 + 3 ^ 40 * 887485 * 2
def baseEnd_887485 : Nat := 202536168291362419802683

theorem tailTrace_887485 : CollatzResearch.WordTrace tailWord_887485 prefixEnd_887485 202536168291362419802683 := by
  unfold tailWord_887485
  simp only [CollatzResearch.WordTrace]
  refine ⟨32369237189800890215975909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21579491459867260143983939 32369237189800890215975909)
  ·
    refine ⟨6069231973087666915495483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32369237189800890215975909 6069231973087666915495483)
    ·
      refine ⟨9103847959631500373243225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6069231973087666915495483 9103847959631500373243225)
      ·
        refine ⟨6827885969723625279932419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9103847959631500373243225 6827885969723625279932419)
        ·
          refine ⟨10241828954585437919898629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6827885969723625279932419 10241828954585437919898629)
          ·
            refine ⟨1920342928984769609980993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10241828954585437919898629 1920342928984769609980993)
            ·
              refine ⟨1440257196738577207485745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1920342928984769609980993 1440257196738577207485745)
              ·
                refine ⟨1080192897553932905614309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1440257196738577207485745 1080192897553932905614309)
                ·
                  refine ⟨202536168291362419802683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1080192897553932905614309 202536168291362419802683)
                  ·
                    rfl

theorem cell21_887485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 2, 2, 4].length) (baseStart_887485 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_887485 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_887485 prefixEnd_887485 := by exact prefixLift 887485
  have htrace : WordTrace (prefixWord ++ tailWord_887485) baseStart_887485 baseEnd_887485 := by
    simpa [prefixWord, tailWord_887485, baseEnd_887485] using wordTrace_append hprefix tailTrace_887485
  have hstable : (prefixWord ++ tailWord_887485).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_887485).length < 2 ^ (prefixWord ++ tailWord_887485).sum := by decide
  have hdescent : baseEnd_887485 < baseStart_887485 := by decide
  rcases family_descends (prefixWord ++ tailWord_887485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_887488 : List Nat := [2, 1, 1, 2, 4, 4, 2, 2, 3]
def baseStart_887488 : Nat := 118140960795 + 887488 * 2 ^ 59
def prefixEnd_887488 : Nat := 4983230072969 + 3 ^ 40 * 887488 * 2
def baseEnd_887488 : Nat := 202536852932235081252677

theorem tailTrace_887488 : CollatzResearch.WordTrace tailWord_887488 prefixEnd_887488 202536852932235081252677 := by
  unfold tailWord_887488
  simp only [CollatzResearch.WordTrace]
  refine ⟨16184673304395010864167559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21579564405860014485556745 16184673304395010864167559)
  ·
    refine ⟨24277009956592516296251339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16184673304395010864167559 24277009956592516296251339)
    ·
      refine ⟨36415514934888774444377009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24277009956592516296251339 36415514934888774444377009)
      ·
        refine ⟨27311636201166580833282757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36415514934888774444377009 27311636201166580833282757)
        ·
          refine ⟨5120931787718733906240517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27311636201166580833282757 5120931787718733906240517)
          ·
            refine ⟨960174710197262607420097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5120931787718733906240517 960174710197262607420097)
            ·
              refine ⟨720131032647946955565073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 960174710197262607420097 720131032647946955565073)
              ·
                refine ⟨540098274485960216673805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 720131032647946955565073 540098274485960216673805)
                ·
                  refine ⟨202536852932235081252677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 540098274485960216673805 202536852932235081252677)
                  ·
                    rfl

theorem cell21_887488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 2, 2, 3].length) (baseStart_887488 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_887488 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_887488 prefixEnd_887488 := by exact prefixLift 887488
  have htrace : WordTrace (prefixWord ++ tailWord_887488) baseStart_887488 baseEnd_887488 := by
    simpa [prefixWord, tailWord_887488, baseEnd_887488] using wordTrace_append hprefix tailTrace_887488
  have hstable : (prefixWord ++ tailWord_887488).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_887488).length < 2 ^ (prefixWord ++ tailWord_887488).sum := by decide
  have hdescent : baseEnd_887488 < baseStart_887488 := by decide
  rcases family_descends (prefixWord ++ tailWord_887488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_887513 : List Nat := [1, 2, 1, 2, 3, 2, 3, 2, 5]
def baseStart_887513 : Nat := 118140960795 + 887513 * 2 ^ 59
def prefixEnd_887513 : Nat := 4983230072969 + 3 ^ 40 * 887513 * 2
def baseEnd_887513 : Nat := 202542558272840593335959

theorem tailTrace_887513 : CollatzResearch.WordTrace tailWord_887513 prefixEnd_887513 202542558272840593335959 := by
  unfold tailWord_887513
  simp only [CollatzResearch.WordTrace]
  refine ⟨32370258433699450997995193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21580172289132967331996795 32370258433699450997995193)
  ·
    refine ⟨24277693825274588248496395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32370258433699450997995193 24277693825274588248496395)
    ·
      refine ⟨36416540737911882372744593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24277693825274588248496395 36416540737911882372744593)
      ·
        refine ⟨27312405553433911779558445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36416540737911882372744593 27312405553433911779558445)
        ·
          refine ⟨10242152082537716917334417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27312405553433911779558445 10242152082537716917334417)
          ·
            refine ⟨7681614061903287688000813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10242152082537716917334417 7681614061903287688000813)
            ·
              refine ⟨2880605273213732883000305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7681614061903287688000813 2880605273213732883000305)
              ·
                refine ⟨2160453954910299662250229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2880605273213732883000305 2160453954910299662250229)
                ·
                  refine ⟨202542558272840593335959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2160453954910299662250229 202542558272840593335959)
                  ·
                    rfl

theorem cell21_887513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 3, 2, 5].length) (baseStart_887513 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_887513 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_887513 prefixEnd_887513 := by exact prefixLift 887513
  have htrace : WordTrace (prefixWord ++ tailWord_887513) baseStart_887513 baseEnd_887513 := by
    simpa [prefixWord, tailWord_887513, baseEnd_887513] using wordTrace_append hprefix tailTrace_887513
  have hstable : (prefixWord ++ tailWord_887513).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_887513).length < 2 ^ (prefixWord ++ tailWord_887513).sum := by decide
  have hdescent : baseEnd_887513 < baseStart_887513 := by decide
  rcases family_descends (prefixWord ++ tailWord_887513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_887575 : List Nat := [1, 1, 3, 4, 3, 1, 1, 7]
def baseStart_887575 : Nat := 118140960795 + 887575 * 2 ^ 59
def prefixEnd_887575 : Nat := 4983230072969 + 3 ^ 40 * 887575 * 2
def baseEnd_887575 : Nat := 67518902505847421100833

theorem tailTrace_887575 : CollatzResearch.WordTrace tailWord_887575 prefixEnd_887575 67518902505847421100833 := by
  unfold tailWord_887575
  simp only [CollatzResearch.WordTrace]
  refine ⟨32372519759474835586752179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21581679839649890391168119 32372519759474835586752179)
  ·
    refine ⟨48558779639212253380128269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32372519759474835586752179 48558779639212253380128269)
    ·
      refine ⟨18209542364704595017548101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48558779639212253380128269 18209542364704595017548101)
      ·
        refine ⟨3414289193382111565790269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18209542364704595017548101 3414289193382111565790269)
        ·
          refine ⟨1280358447518291837171351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3414289193382111565790269 1280358447518291837171351)
          ·
            refine ⟨1920537671277437755757027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1280358447518291837171351 1920537671277437755757027)
            ·
              refine ⟨2880806506916156633635541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1920537671277437755757027 2880806506916156633635541)
              ·
                refine ⟨67518902505847421100833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2880806506916156633635541 67518902505847421100833)
                ·
                  rfl

theorem cell21_887575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 1, 7].length) (baseStart_887575 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_887575 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_887575 prefixEnd_887575 := by exact prefixLift 887575
  have htrace : WordTrace (prefixWord ++ tailWord_887575) baseStart_887575 baseEnd_887575 := by
    simpa [prefixWord, tailWord_887575, baseEnd_887575] using wordTrace_append hprefix tailTrace_887575
  have hstable : (prefixWord ++ tailWord_887575).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_887575).length < 2 ^ (prefixWord ++ tailWord_887575).sum := by decide
  have hdescent : baseEnd_887575 < baseStart_887575 := by decide
  rcases family_descends (prefixWord ++ tailWord_887575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_887581 : List Nat := [1, 4, 2, 4, 1, 2, 1, 3, 3]
def baseStart_887581 : Nat := 118140960795 + 887581 * 2 ^ 59
def prefixEnd_887581 : Nat := 4983230072969 + 3 ^ 40 * 887581 * 2
def baseEnd_887581 : Nat := 202558076799287586202487

theorem tailTrace_887581 : CollatzResearch.WordTrace tailWord_887581 prefixEnd_887581 202558076799287586202487 := by
  unfold tailWord_887581
  simp only [CollatzResearch.WordTrace]
  refine ⟨32372738597453098611470597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21581825731635399074313731 32372738597453098611470597)
  ·
    refine ⟨6069888487022455989650737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32372738597453098611470597 6069888487022455989650737)
    ·
      refine ⟨4552416365266841992238053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6069888487022455989650737 4552416365266841992238053)
      ·
        refine ⟨853578068487532873544635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4552416365266841992238053 853578068487532873544635)
        ·
          refine ⟨1280367102731299310316953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 853578068487532873544635 1280367102731299310316953)
          ·
            refine ⟨960275327048474482737715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1280367102731299310316953 960275327048474482737715)
            ·
              refine ⟨1440412990572711724106573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 960275327048474482737715 1440412990572711724106573)
              ·
                refine ⟨540154871464766896539965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1440412990572711724106573 540154871464766896539965)
                ·
                  refine ⟨202558076799287586202487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 540154871464766896539965 202558076799287586202487)
                  ·
                    rfl

theorem cell21_887581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 1, 3, 3].length) (baseStart_887581 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_887581 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_887581 prefixEnd_887581 := by exact prefixLift 887581
  have htrace : WordTrace (prefixWord ++ tailWord_887581) baseStart_887581 baseEnd_887581 := by
    simpa [prefixWord, tailWord_887581, baseEnd_887581] using wordTrace_append hprefix tailTrace_887581
  have hstable : (prefixWord ++ tailWord_887581).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_887581).length < 2 ^ (prefixWord ++ tailWord_887581).sum := by decide
  have hdescent : baseEnd_887581 < baseStart_887581 := by decide
  rcases family_descends (prefixWord ++ tailWord_887581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_887634 : List Nat := [3, 2, 2, 1, 1, 2, 1, 9]
def baseStart_887634 : Nat := 118140960795 + 887634 * 2 ^ 59
def prefixEnd_887634 : Nat := 4983230072969 + 3 ^ 40 * 887634 * 2
def baseEnd_887634 : Nat := 67523390707123757273015

theorem tailTrace_887634 : CollatzResearch.WordTrace tailWord_887634 prefixEnd_887634 67523390707123757273015 := by
  unfold tailWord_887634
  simp only [CollatzResearch.WordTrace]
  refine ⟨8093667916565272165787489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21583114444174059108766637 8093667916565272165787489)
  ·
    refine ⟨6070250937423954124340617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8093667916565272165787489 6070250937423954124340617)
    ·
      refine ⟨4552688203067965593255463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6070250937423954124340617 4552688203067965593255463)
      ·
        refine ⟨6829032304601948389883195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4552688203067965593255463 6829032304601948389883195)
        ·
          refine ⟨10243548456902922584824793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6829032304601948389883195 10243548456902922584824793)
          ·
            refine ⟨7682661342677191938618595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10243548456902922584824793 7682661342677191938618595)
            ·
              refine ⟨11523992014015787907927893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7682661342677191938618595 11523992014015787907927893)
              ·
                refine ⟨67523390707123757273015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 11523992014015787907927893 67523390707123757273015)
                ·
                  rfl

theorem cell21_887634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 9].length) (baseStart_887634 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_887634 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_887634 prefixEnd_887634 := by exact prefixLift 887634
  have htrace : WordTrace (prefixWord ++ tailWord_887634) baseStart_887634 baseEnd_887634 := by
    simpa [prefixWord, tailWord_887634, baseEnd_887634] using wordTrace_append hprefix tailTrace_887634
  have hstable : (prefixWord ++ tailWord_887634).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_887634).length < 2 ^ (prefixWord ++ tailWord_887634).sum := by decide
  have hdescent : baseEnd_887634 < baseStart_887634 := by decide
  rcases family_descends (prefixWord ++ tailWord_887634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_887713 : List Nat := [1, 2, 3, 4, 1, 1, 3, 2, 4]
def baseStart_887713 : Nat := 118140960795 + 887713 * 2 ^ 59
def prefixEnd_887713 : Nat := 4983230072969 + 3 ^ 40 * 887713 * 2
def baseEnd_887713 : Nat := 202588200997684690002217

theorem tailTrace_887713 : CollatzResearch.WordTrace tailWord_887713 prefixEnd_887713 202588200997684690002217 := by
  unfold tailWord_887713
  simp only [CollatzResearch.WordTrace]
  refine ⟨32377553032974885155275793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21585035355316590103517195 32377553032974885155275793)
  ·
    refine ⟨24283164774731163866456845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32377553032974885155275793 24283164774731163866456845)
    ·
      refine ⟨9106186790524186449921317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24283164774731163866456845 9106186790524186449921317)
      ·
        refine ⟨1707410023223284959360247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9106186790524186449921317 1707410023223284959360247)
        ·
          refine ⟨2561115034834927439040371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1707410023223284959360247 2561115034834927439040371)
          ·
            refine ⟨3841672552252391158560557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2561115034834927439040371 3841672552252391158560557)
            ·
              refine ⟨1440627207094646684460209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3841672552252391158560557 1440627207094646684460209)
              ·
                refine ⟨1080470405320985013345157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1440627207094646684460209 1080470405320985013345157)
                ·
                  refine ⟨202588200997684690002217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1080470405320985013345157 202588200997684690002217)
                  ·
                    rfl

theorem cell21_887713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 3, 2, 4].length) (baseStart_887713 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_887713 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_887713 prefixEnd_887713 := by exact prefixLift 887713
  have htrace : WordTrace (prefixWord ++ tailWord_887713) baseStart_887713 baseEnd_887713 := by
    simpa [prefixWord, tailWord_887713, baseEnd_887713] using wordTrace_append hprefix tailTrace_887713
  have hstable : (prefixWord ++ tailWord_887713).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_887713).length < 2 ^ (prefixWord ++ tailWord_887713).sum := by decide
  have hdescent : baseEnd_887713 < baseStart_887713 := by decide
  rcases family_descends (prefixWord ++ tailWord_887713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_887724 : List Nat := [2, 2, 1, 1, 1, 1, 2, 2, 9]
def baseStart_887724 : Nat := 118140960795 + 887724 * 2 ^ 59
def prefixEnd_887724 : Nat := 4983230072969 + 3 ^ 40 * 887724 * 2
def baseEnd_887724 : Nat := 202590711347551115318861

theorem tailTrace_887724 : CollatzResearch.WordTrace tailWord_887724 prefixEnd_887724 202590711347551115318861 := by
  unfold tailWord_887724
  simp only [CollatzResearch.WordTrace]
  refine ⟨16188977117967517016963113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21585302823956689355950817 16188977117967517016963113)
  ·
    refine ⟨12141732838475637762722335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16188977117967517016963113 12141732838475637762722335)
    ·
      refine ⟨18212599257713456644083503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12141732838475637762722335 18212599257713456644083503)
      ·
        refine ⟨27318898886570184966125255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18212599257713456644083503 27318898886570184966125255)
        ·
          refine ⟨40978348329855277449187883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27318898886570184966125255 40978348329855277449187883)
          ·
            refine ⟨61467522494782916173781825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40978348329855277449187883 61467522494782916173781825)
            ·
              refine ⟨46100641871087187130336369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61467522494782916173781825 46100641871087187130336369)
              ·
                refine ⟨34575481403315390347752277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46100641871087187130336369 34575481403315390347752277)
                ·
                  refine ⟨202590711347551115318861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 34575481403315390347752277 202590711347551115318861)
                  ·
                    rfl

theorem cell21_887724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 9].length) (baseStart_887724 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_887724 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_887724 prefixEnd_887724 := by exact prefixLift 887724
  have htrace : WordTrace (prefixWord ++ tailWord_887724) baseStart_887724 baseEnd_887724 := by
    simpa [prefixWord, tailWord_887724, baseEnd_887724] using wordTrace_append hprefix tailTrace_887724
  have hstable : (prefixWord ++ tailWord_887724).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_887724).length < 2 ^ (prefixWord ++ tailWord_887724).sum := by decide
  have hdescent : baseEnd_887724 < baseStart_887724 := by decide
  rcases family_descends (prefixWord ++ tailWord_887724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_887755 : List Nat := [1, 1, 1, 1, 3, 5, 1, 2, 6]
def baseStart_887755 : Nat := 118140960795 + 887755 * 2 ^ 59
def prefixEnd_887755 : Nat := 4983230072969 + 3 ^ 40 * 887755 * 2
def baseEnd_887755 : Nat := 202597785969901950302131

theorem tailTrace_887755 : CollatzResearch.WordTrace tailWord_887755 prefixEnd_887755 202597785969901950302131 := by
  unfold tailWord_887755
  simp only [CollatzResearch.WordTrace]
  refine ⟨32379084898822726328304719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21586056599215150885536479 32379084898822726328304719)
  ·
    refine ⟨48568627348234089492457079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32379084898822726328304719 48568627348234089492457079)
    ·
      refine ⟨72852941022351134238685619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48568627348234089492457079 72852941022351134238685619)
      ·
        refine ⟨109279411533526701358028429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72852941022351134238685619 109279411533526701358028429)
        ·
          refine ⟨40979779325072513009260661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109279411533526701358028429 40979779325072513009260661)
          ·
            refine ⟨3841854311725548094618187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 40979779325072513009260661 3841854311725548094618187)
            ·
              refine ⟨5762781467588322141927281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3841854311725548094618187 5762781467588322141927281)
              ·
                refine ⟨4322086100691241606445461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5762781467588322141927281 4322086100691241606445461)
                ·
                  refine ⟨202597785969901950302131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4322086100691241606445461 202597785969901950302131)
                  ·
                    rfl

theorem cell21_887755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 2, 6].length) (baseStart_887755 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_887755 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_887755 prefixEnd_887755 := by exact prefixLift 887755
  have htrace : WordTrace (prefixWord ++ tailWord_887755) baseStart_887755 baseEnd_887755 := by
    simpa [prefixWord, tailWord_887755, baseEnd_887755] using wordTrace_append hprefix tailTrace_887755
  have hstable : (prefixWord ++ tailWord_887755).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_887755).length < 2 ^ (prefixWord ++ tailWord_887755).sum := by decide
  have hdescent : baseEnd_887755 < baseStart_887755 := by decide
  rcases family_descends (prefixWord ++ tailWord_887755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_887775 : List Nat := [1, 1, 2, 3, 6, 1, 1, 1, 5]
def baseStart_887775 : Nat := 118140960795 + 887775 * 2 ^ 59
def prefixEnd_887775 : Nat := 4983230072969 + 3 ^ 40 * 887775 * 2
def baseEnd_887775 : Nat := 202602350242386359968757

theorem tailTrace_887775 : CollatzResearch.WordTrace tailWord_887775 prefixEnd_887775 202602350242386359968757 := by
  unfold tailWord_887775
  simp only [CollatzResearch.WordTrace]
  refine ⟨32379814358750269744032779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21586542905833513162688519 32379814358750269744032779)
  ·
    refine ⟨48569721538125404616049169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32379814358750269744032779 48569721538125404616049169)
    ·
      refine ⟨36427291153594053462036877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48569721538125404616049169 36427291153594053462036877)
      ·
        refine ⟨13660234182597770048263829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36427291153594053462036877 13660234182597770048263829)
        ·
          refine ⟨640323477309270471012367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 13660234182597770048263829 640323477309270471012367)
          ·
            refine ⟨960485215963905706518551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 640323477309270471012367 960485215963905706518551)
            ·
              refine ⟨1440727823945858559777827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 960485215963905706518551 1440727823945858559777827)
              ·
                refine ⟨2161091735918787839666741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1440727823945858559777827 2161091735918787839666741)
                ·
                  refine ⟨202602350242386359968757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2161091735918787839666741 202602350242386359968757)
                  ·
                    rfl

theorem cell21_887775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 1, 1, 5].length) (baseStart_887775 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_887775 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_887775 prefixEnd_887775 := by exact prefixLift 887775
  have htrace : WordTrace (prefixWord ++ tailWord_887775) baseStart_887775 baseEnd_887775 := by
    simpa [prefixWord, tailWord_887775, baseEnd_887775] using wordTrace_append hprefix tailTrace_887775
  have hstable : (prefixWord ++ tailWord_887775).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_887775).length < 2 ^ (prefixWord ++ tailWord_887775).sum := by decide
  have hdescent : baseEnd_887775 < baseStart_887775 := by decide
  rcases family_descends (prefixWord ++ tailWord_887775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_887786 : List Nat := [3, 1, 3, 1, 2, 2, 1, 8]
def baseStart_887786 : Nat := 118140960795 + 887786 * 2 ^ 59
def prefixEnd_887786 : Nat := 4983230072969 + 3 ^ 40 * 887786 * 2
def baseEnd_887786 : Nat := 67534953530750928428467

theorem tailTrace_887786 : CollatzResearch.WordTrace tailWord_887786 prefixEnd_887786 67534953530750928428467 := by
  unfold tailWord_887786
  simp only [CollatzResearch.WordTrace]
  refine ⟨8095053890427604655670803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21586810374473612415122141 8095053890427604655670803)
  ·
    refine ⟨12142580835641406983506205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8095053890427604655670803 12142580835641406983506205)
    ·
      refine ⟨4553467813365527618814827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12142580835641406983506205 4553467813365527618814827)
      ·
        refine ⟨6830201720048291428222241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4553467813365527618814827 6830201720048291428222241)
        ·
          refine ⟨5122651290036218571166681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6830201720048291428222241 5122651290036218571166681)
          ·
            refine ⟨3841988467527163928375011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5122651290036218571166681 3841988467527163928375011)
            ·
              refine ⟨5762982701290745892562517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3841988467527163928375011 5762982701290745892562517)
              ·
                refine ⟨67534953530750928428467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5762982701290745892562517 67534953530750928428467)
                ·
                  rfl

theorem cell21_887786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 8].length) (baseStart_887786 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_887786 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_887786 prefixEnd_887786 := by exact prefixLift 887786
  have htrace : WordTrace (prefixWord ++ tailWord_887786) baseStart_887786 baseEnd_887786 := by
    simpa [prefixWord, tailWord_887786, baseEnd_887786] using wordTrace_append hprefix tailTrace_887786
  have hstable : (prefixWord ++ tailWord_887786).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_887786).length < 2 ^ (prefixWord ++ tailWord_887786).sum := by decide
  have hdescent : baseEnd_887786 < baseStart_887786 := by decide
  rcases family_descends (prefixWord ++ tailWord_887786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_887800 : List Nat := [2, 1, 2, 1, 1, 3, 1, 3, 7]
def baseStart_887800 : Nat := 118140960795 + 887800 * 2 ^ 59
def prefixEnd_887800 : Nat := 4983230072969 + 3 ^ 40 * 887800 * 2
def baseEnd_887800 : Nat := 202608055582991872052039

theorem tailTrace_887800 : CollatzResearch.WordTrace tailWord_887800 prefixEnd_887800 202608055582991872052039 := by
  unfold tailWord_887800
  simp only [CollatzResearch.WordTrace]
  refine ⟨16190363091829849506846427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21587150789106466009128569 16190363091829849506846427)
  ·
    refine ⟨24285544637744774260269641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16190363091829849506846427 24285544637744774260269641)
    ·
      refine ⟨18214158478308580695202231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24285544637744774260269641 18214158478308580695202231)
      ·
        refine ⟨27321237717462871042803347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18214158478308580695202231 27321237717462871042803347)
        ·
          refine ⟨40981856576194306564205021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27321237717462871042803347 40981856576194306564205021)
          ·
            refine ⟨15368196216072864961576883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40981856576194306564205021 15368196216072864961576883)
            ·
              refine ⟨23052294324109297442365325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15368196216072864961576883 23052294324109297442365325)
              ·
                refine ⟨8644610371540986540886997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23052294324109297442365325 8644610371540986540886997)
                ·
                  refine ⟨202608055582991872052039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8644610371540986540886997 202608055582991872052039)
                  ·
                    rfl

theorem cell21_887800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 3, 7].length) (baseStart_887800 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_887800 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_887800 prefixEnd_887800 := by exact prefixLift 887800
  have htrace : WordTrace (prefixWord ++ tailWord_887800) baseStart_887800 baseEnd_887800 := by
    simpa [prefixWord, tailWord_887800, baseEnd_887800] using wordTrace_append hprefix tailTrace_887800
  have hstable : (prefixWord ++ tailWord_887800).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_887800).length < 2 ^ (prefixWord ++ tailWord_887800).sum := by decide
  have hdescent : baseEnd_887800 < baseStart_887800 := by decide
  rcases family_descends (prefixWord ++ tailWord_887800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_887834 : List Nat := [3, 1, 1, 3, 1, 2, 3, 4, 3]
def baseStart_887834 : Nat := 118140960795 + 887834 * 2 ^ 59
def prefixEnd_887834 : Nat := 4983230072969 + 3 ^ 40 * 887834 * 2
def baseEnd_887834 : Nat := 202615814846215368485303

theorem tailTrace_887834 : CollatzResearch.WordTrace tailWord_887834 prefixEnd_887834 202615814846215368485303 := by
  unfold tailWord_887834
  simp only [CollatzResearch.WordTrace]
  refine ⟨8095491566384130705107639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21587977510357681880287037 8095491566384130705107639)
  ·
    refine ⟨12143237349576196057661459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8095491566384130705107639 12143237349576196057661459)
    ·
      refine ⟨18214856024364294086492189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12143237349576196057661459 18214856024364294086492189)
      ·
        refine ⟨6830571009136610282434571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18214856024364294086492189 6830571009136610282434571)
        ·
          refine ⟨10245856513704915423651857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6830571009136610282434571 10245856513704915423651857)
          ·
            refine ⟨7684392385278686567738893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10245856513704915423651857 7684392385278686567738893)
            ·
              refine ⟨2881647144479507462902085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7684392385278686567738893 2881647144479507462902085)
              ·
                refine ⟨540308839589907649294141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2881647144479507462902085 540308839589907649294141)
                ·
                  refine ⟨202615814846215368485303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 540308839589907649294141 202615814846215368485303)
                  ·
                    rfl

theorem cell21_887834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 3, 4, 3].length) (baseStart_887834 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_887834 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_887834 prefixEnd_887834 := by exact prefixLift 887834
  have htrace : WordTrace (prefixWord ++ tailWord_887834) baseStart_887834 baseEnd_887834 := by
    simpa [prefixWord, tailWord_887834, baseEnd_887834] using wordTrace_append hprefix tailTrace_887834
  have hstable : (prefixWord ++ tailWord_887834).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_887834).length < 2 ^ (prefixWord ++ tailWord_887834).sum := by decide
  have hdescent : baseEnd_887834 < baseStart_887834 := by decide
  rcases family_descends (prefixWord ++ tailWord_887834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_887893 : List Nat := [1, 3, 2, 2, 1, 2, 4, 1, 5]
def baseStart_887893 : Nat := 118140960795 + 887893 * 2 ^ 59
def prefixEnd_887893 : Nat := 4983230072969 + 3 ^ 40 * 887893 * 2
def baseEnd_887893 : Nat := 202629279450044377001849

theorem tailTrace_887893 : CollatzResearch.WordTrace tailWord_887893 prefixEnd_887893 202629279450044377001849 := by
  unfold tailWord_887893
  simp only [CollatzResearch.WordTrace]
  refine ⟨32384118172322775896828333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21589412114881850597885555 32384118172322775896828333)
  ·
    refine ⟨12144044314621040961310625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32384118172322775896828333 12144044314621040961310625)
    ·
      refine ⟨9108033235965780720982969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12144044314621040961310625 9108033235965780720982969)
      ·
        refine ⟨6831024926974335540737227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9108033235965780720982969 6831024926974335540737227)
        ·
          refine ⟨10246537390461503311105841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6831024926974335540737227 10246537390461503311105841)
          ·
            refine ⟨7684903042846127483329381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10246537390461503311105841 7684903042846127483329381)
            ·
              refine ⟨1440919320533648903124259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7684903042846127483329381 1440919320533648903124259)
              ·
                refine ⟨2161378980800473354686389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1440919320533648903124259 2161378980800473354686389)
                ·
                  refine ⟨202629279450044377001849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2161378980800473354686389 202629279450044377001849)
                  ·
                    rfl

theorem cell21_887893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 4, 1, 5].length) (baseStart_887893 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_887893 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_887893 prefixEnd_887893 := by exact prefixLift 887893
  have htrace : WordTrace (prefixWord ++ tailWord_887893) baseStart_887893 baseEnd_887893 := by
    simpa [prefixWord, tailWord_887893, baseEnd_887893] using wordTrace_append hprefix tailTrace_887893
  have hstable : (prefixWord ++ tailWord_887893).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_887893).length < 2 ^ (prefixWord ++ tailWord_887893).sum := by decide
  have hdescent : baseEnd_887893 < baseStart_887893 := by decide
  rcases family_descends (prefixWord ++ tailWord_887893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_887944 : List Nat := [2, 1, 3, 4, 2, 1, 3, 2, 3]
def baseStart_887944 : Nat := 118140960795 + 887944 * 2 ^ 59
def prefixEnd_887944 : Nat := 4983230072969 + 3 ^ 40 * 887944 * 2
def baseEnd_887944 : Nat := 202640918344879621651745

theorem tailTrace_887944 : CollatzResearch.WordTrace tailWord_887944 prefixEnd_887944 202640918344879621651745 := by
  unfold tailWord_887944
  simp only [CollatzResearch.WordTrace]
  refine ⟨16192989147569005803467443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21590652196758674404623257 16192989147569005803467443)
  ·
    refine ⟨24289483721353508705201165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16192989147569005803467443 24289483721353508705201165)
    ·
      refine ⟨9108556395507565764450437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24289483721353508705201165 9108556395507565764450437)
      ·
        refine ⟨1707854324157668580834457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9108556395507565764450437 1707854324157668580834457)
        ·
          refine ⟨1280890743118251435625843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1707854324157668580834457 1280890743118251435625843)
          ·
            refine ⟨1921336114677377153438765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1280890743118251435625843 1921336114677377153438765)
            ·
              refine ⟨720501043004016432539537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1921336114677377153438765 720501043004016432539537)
              ·
                refine ⟨540375782253012324404653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 720501043004016432539537 540375782253012324404653)
                ·
                  refine ⟨202640918344879621651745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 540375782253012324404653 202640918344879621651745)
                  ·
                    rfl

theorem cell21_887944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 3, 2, 3].length) (baseStart_887944 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_887944 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_887944 prefixEnd_887944 := by exact prefixLift 887944
  have htrace : WordTrace (prefixWord ++ tailWord_887944) baseStart_887944 baseEnd_887944 := by
    simpa [prefixWord, tailWord_887944, baseEnd_887944] using wordTrace_append hprefix tailTrace_887944
  have hstable : (prefixWord ++ tailWord_887944).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_887944).length < 2 ^ (prefixWord ++ tailWord_887944).sum := by decide
  have hdescent : baseEnd_887944 < baseStart_887944 := by decide
  rcases family_descends (prefixWord ++ tailWord_887944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_887952 : List Nat := [2, 1, 1, 1, 1, 1, 4, 5, 5]
def baseStart_887952 : Nat := 118140960795 + 887952 * 2 ^ 59
def prefixEnd_887952 : Nat := 4983230072969 + 3 ^ 40 * 887952 * 2
def baseEnd_887952 : Nat := 202642744053873385518395

theorem tailTrace_887952 : CollatzResearch.WordTrace tailWord_887952 prefixEnd_887952 202642744053873385518395 := by
  unfold tailWord_887952
  simp only [CollatzResearch.WordTrace]
  refine ⟨16193135039554514486613055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21590846719406019315484073 16193135039554514486613055)
  ·
    refine ⟨24289702559331771729919583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16193135039554514486613055 24289702559331771729919583)
    ·
      refine ⟨36434553838997657594879375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24289702559331771729919583 36434553838997657594879375)
      ·
        refine ⟨54651830758496486392319063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36434553838997657594879375 54651830758496486392319063)
        ·
          refine ⟨81977746137744729588478595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54651830758496486392319063 81977746137744729588478595)
          ·
            refine ⟨122966619206617094382717893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81977746137744729588478595 122966619206617094382717893)
            ·
              refine ⟨23056241101240705196759605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 122966619206617094382717893 23056241101240705196759605)
              ·
                refine ⟨2161522603241316112196213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23056241101240705196759605 2161522603241316112196213)
                ·
                  refine ⟨202642744053873385518395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2161522603241316112196213 202642744053873385518395)
                  ·
                    rfl

theorem cell21_887952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 5, 5].length) (baseStart_887952 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_887952 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_887952 prefixEnd_887952 := by exact prefixLift 887952
  have htrace : WordTrace (prefixWord ++ tailWord_887952) baseStart_887952 baseEnd_887952 := by
    simpa [prefixWord, tailWord_887952, baseEnd_887952] using wordTrace_append hprefix tailTrace_887952
  have hstable : (prefixWord ++ tailWord_887952).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_887952).length < 2 ^ (prefixWord ++ tailWord_887952).sum := by decide
  have hdescent : baseEnd_887952 < baseStart_887952 := by decide
  rcases family_descends (prefixWord ++ tailWord_887952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_888006 : List Nat := [6, 1, 2, 2, 1, 2, 1, 6]
def baseStart_888006 : Nat := 118140960795 + 888006 * 2 ^ 59
def prefixEnd_888006 : Nat := 4983230072969 + 3 ^ 40 * 888006 * 2
def baseEnd_888006 : Nat := 67551689196527097206095

theorem tailTrace_888006 : CollatzResearch.WordTrace tailWord_888006 prefixEnd_888006 67551689196527097206095 := by
  unfold tailWord_888006
  simp only [CollatzResearch.WordTrace]
  refine ⟨1012132488153543631115371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 21592159747275597463794581 1012132488153543631115371)
  ·
    refine ⟨1518198732230315446673057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1012132488153543631115371 1518198732230315446673057)
    ·
      refine ⟨1138649049172736585004793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1518198732230315446673057 1138649049172736585004793)
      ·
        refine ⟨853986786879552438753595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1138649049172736585004793 853986786879552438753595)
        ·
          refine ⟨1280980180319328658130393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 853986786879552438753595 1280980180319328658130393)
          ·
            refine ⟨960735135239496493597795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1280980180319328658130393 960735135239496493597795)
            ·
              refine ⟨1441102702859244740396693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 960735135239496493597795 1441102702859244740396693)
              ·
                refine ⟨67551689196527097206095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1441102702859244740396693 67551689196527097206095)
                ·
                  rfl

theorem cell21_888006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 1, 6].length) (baseStart_888006 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_888006 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_888006 prefixEnd_888006 := by exact prefixLift 888006
  have htrace : WordTrace (prefixWord ++ tailWord_888006) baseStart_888006 baseEnd_888006 := by
    simpa [prefixWord, tailWord_888006, baseEnd_888006] using wordTrace_append hprefix tailTrace_888006
  have hstable : (prefixWord ++ tailWord_888006).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_888006).length < 2 ^ (prefixWord ++ tailWord_888006).sum := by decide
  have hdescent : baseEnd_888006 < baseStart_888006 := by decide
  rcases family_descends (prefixWord ++ tailWord_888006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_888062 : List Nat := [4, 2, 2, 1, 1, 3, 2, 1, 5]
def baseStart_888062 : Nat := 118140960795 + 888062 * 2 ^ 59
def prefixEnd_888062 : Nat := 4983230072969 + 3 ^ 40 * 888062 * 2
def baseEnd_888062 : Nat := 202667847552537638684837

theorem tailTrace_888062 : CollatzResearch.WordTrace tailWord_888062 prefixEnd_888062 202667847552537638684837 := by
  unfold tailWord_888062
  simp only [CollatzResearch.WordTrace]
  refine ⟨4048785263588814719966305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21593521405807011839820293 4048785263588814719966305)
  ·
    refine ⟨3036588947691611039974729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4048785263588814719966305 3036588947691611039974729)
    ·
      refine ⟨2277441710768708279981047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3036588947691611039974729 2277441710768708279981047)
      ·
        refine ⟨3416162566153062419971571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2277441710768708279981047 3416162566153062419971571)
        ·
          refine ⟨5124243849229593629957357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3416162566153062419971571 5124243849229593629957357)
          ·
            refine ⟨1921591443461097611234009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5124243849229593629957357 1921591443461097611234009)
            ·
              refine ⟨1441193582595823208425507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1921591443461097611234009 1441193582595823208425507)
              ·
                refine ⟨2161790373893734812638261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1441193582595823208425507 2161790373893734812638261)
                ·
                  refine ⟨202667847552537638684837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2161790373893734812638261 202667847552537638684837)
                  ·
                    rfl

theorem cell21_888062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 2, 1, 5].length) (baseStart_888062 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_888062 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_888062 prefixEnd_888062 := by exact prefixLift 888062
  have htrace : WordTrace (prefixWord ++ tailWord_888062) baseStart_888062 baseEnd_888062 := by
    simpa [prefixWord, tailWord_888062, baseEnd_888062] using wordTrace_append hprefix tailTrace_888062
  have hstable : (prefixWord ++ tailWord_888062).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_888062).length < 2 ^ (prefixWord ++ tailWord_888062).sum := by decide
  have hdescent : baseEnd_888062 < baseStart_888062 := by decide
  rcases family_descends (prefixWord ++ tailWord_888062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_888073 : List Nat := [1, 2, 1, 1, 3, 3, 2, 8]
def baseStart_888073 : Nat := 118140960795 + 888073 * 2 ^ 59
def prefixEnd_888073 : Nat := 4983230072969 + 3 ^ 40 * 888073 * 2
def baseEnd_888073 : Nat := 67556785967468021333827

theorem tailTrace_888073 : CollatzResearch.WordTrace tailWord_888073 prefixEnd_888073 67556785967468021333827 := by
  unfold tailWord_888073
  simp only [CollatzResearch.WordTrace]
  refine ⟨32390683311670666638380873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21593788874447111092253915 32390683311670666638380873)
  ·
    refine ⟨24293012483752999978785655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32390683311670666638380873 24293012483752999978785655)
    ·
      refine ⟨36439518725629499968178483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24293012483752999978785655 36439518725629499968178483)
      ·
        refine ⟨54659278088444249952267725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36439518725629499968178483 54659278088444249952267725)
        ·
          refine ⟨20497229283166593732100397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54659278088444249952267725 20497229283166593732100397)
          ·
            refine ⟨7686460981187472649537649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20497229283166593732100397 7686460981187472649537649)
            ·
              refine ⟨5764845735890604487153237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7686460981187472649537649 5764845735890604487153237)
              ·
                refine ⟨67556785967468021333827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5764845735890604487153237 67556785967468021333827)
                ·
                  rfl

theorem cell21_888073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 8].length) (baseStart_888073 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_888073 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_888073 prefixEnd_888073 := by exact prefixLift 888073
  have htrace : WordTrace (prefixWord ++ tailWord_888073) baseStart_888073 baseEnd_888073 := by
    simpa [prefixWord, tailWord_888073, baseEnd_888073] using wordTrace_append hprefix tailTrace_888073
  have hstable : (prefixWord ++ tailWord_888073).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_888073).length < 2 ^ (prefixWord ++ tailWord_888073).sum := by decide
  have hdescent : baseEnd_888073 < baseStart_888073 := by decide
  rcases family_descends (prefixWord ++ tailWord_888073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_888082 : List Nat := [3, 2, 4, 2, 2, 1, 2, 5]
def baseStart_888082 : Nat := 118140960795 + 888082 * 2 ^ 59
def prefixEnd_888082 : Nat := 4983230072969 + 3 ^ 40 * 888082 * 2
def baseEnd_888082 : Nat := 67557470608340682783821

theorem tailTrace_888082 : CollatzResearch.WordTrace tailWord_888082 prefixEnd_888082 67557470608340682783821 := by
  unfold tailWord_888082
  simp only [CollatzResearch.WordTrace]
  refine ⟨8097752892159515293864625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21594007712425374116972333 8097752892159515293864625)
  ·
    refine ⟨6073314669119636470398469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8097752892159515293864625 6073314669119636470398469)
    ·
      refine ⟨1138746500459931838199713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6073314669119636470398469 1138746500459931838199713)
      ·
        refine ⟨854059875344948878649785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1138746500459931838199713 854059875344948878649785)
        ·
          refine ⟨640544906508711658987339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 854059875344948878649785 640544906508711658987339)
          ·
            refine ⟨960817359763067488481009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 640544906508711658987339 960817359763067488481009)
            ·
              refine ⟨720613019822300616360757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 960817359763067488481009 720613019822300616360757)
              ·
                refine ⟨67557470608340682783821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 720613019822300616360757 67557470608340682783821)
                ·
                  rfl

theorem cell21_888082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 2, 5].length) (baseStart_888082 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_888082 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_888082 prefixEnd_888082 := by exact prefixLift 888082
  have htrace : WordTrace (prefixWord ++ tailWord_888082) baseStart_888082 baseEnd_888082 := by
    simpa [prefixWord, tailWord_888082, baseEnd_888082] using wordTrace_append hprefix tailTrace_888082
  have hstable : (prefixWord ++ tailWord_888082).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_888082).length < 2 ^ (prefixWord ++ tailWord_888082).sum := by decide
  have hdescent : baseEnd_888082 < baseStart_888082 := by decide
  rcases family_descends (prefixWord ++ tailWord_888082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_888090 : List Nat := [3, 1, 1, 3, 3, 2, 1, 7]
def baseStart_888090 : Nat := 118140960795 + 888090 * 2 ^ 59
def prefixEnd_888090 : Nat := 4983230072969 + 3 ^ 40 * 888090 * 2
def baseEnd_888090 : Nat := 67558079178005270739371

theorem tailTrace_888090 : CollatzResearch.WordTrace tailWord_888090 prefixEnd_888090 67558079178005270739371 := by
  unfold tailWord_888090
  simp only [CollatzResearch.WordTrace]
  refine ⟨8097825838152269635437431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21594202235072719027833149 8097825838152269635437431)
  ·
    refine ⟨12146738757228404453156147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8097825838152269635437431 12146738757228404453156147)
    ·
      refine ⟨18220108135842606679734221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12146738757228404453156147 18220108135842606679734221)
      ·
        refine ⟨6832540550940977504900333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18220108135842606679734221 6832540550940977504900333)
        ·
          refine ⟨2562202706602866564337625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6832540550940977504900333 2562202706602866564337625)
          ·
            refine ⟨1921652029952149923253219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2562202706602866564337625 1921652029952149923253219)
            ·
              refine ⟨2882478044928224884879829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1921652029952149923253219 2882478044928224884879829)
              ·
                refine ⟨67558079178005270739371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2882478044928224884879829 67558079178005270739371)
                ·
                  rfl

theorem cell21_888090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 1, 7].length) (baseStart_888090 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_888090 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_888090 prefixEnd_888090 := by exact prefixLift 888090
  have htrace : WordTrace (prefixWord ++ tailWord_888090) baseStart_888090 baseEnd_888090 := by
    simpa [prefixWord, tailWord_888090, baseEnd_888090] using wordTrace_append hprefix tailTrace_888090
  have hstable : (prefixWord ++ tailWord_888090).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_888090).length < 2 ^ (prefixWord ++ tailWord_888090).sum := by decide
  have hdescent : baseEnd_888090 < baseStart_888090 := by decide
  rcases family_descends (prefixWord ++ tailWord_888090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_888096 : List Nat := [2, 1, 1, 5, 4, 1, 1, 3, 3]
def baseStart_888096 : Nat := 118140960795 + 888096 * 2 ^ 59
def prefixEnd_888096 : Nat := 4983230072969 + 3 ^ 40 * 888096 * 2
def baseEnd_888096 : Nat := 202675606815761135118101

theorem tailTrace_888096 : CollatzResearch.WordTrace tailWord_888096 prefixEnd_888096 202675606815761135118101 := by
  unfold tailWord_888096
  simp only [CollatzResearch.WordTrace]
  refine ⟨16195761095293670783234071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21594348127058227710978761 16195761095293670783234071)
  ·
    refine ⟨24293641642940506174851107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16195761095293670783234071 24293641642940506174851107)
    ·
      refine ⟨36440462464410759262276661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24293641642940506174851107 36440462464410759262276661)
      ·
        refine ⟨3416293356038508680838437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 36440462464410759262276661 3416293356038508680838437)
        ·
          refine ⟨640555004257220377657207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3416293356038508680838437 640555004257220377657207)
          ·
            refine ⟨960832506385830566485811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 640555004257220377657207 960832506385830566485811)
            ·
              refine ⟨1441248759578745849728717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 960832506385830566485811 1441248759578745849728717)
              ·
                refine ⟨540468284842029693648269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1441248759578745849728717 540468284842029693648269)
                ·
                  refine ⟨202675606815761135118101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 540468284842029693648269 202675606815761135118101)
                  ·
                    rfl

theorem cell21_888096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 1, 3, 3].length) (baseStart_888096 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_888096 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_888096 prefixEnd_888096 := by exact prefixLift 888096
  have htrace : WordTrace (prefixWord ++ tailWord_888096) baseStart_888096 baseEnd_888096 := by
    simpa [prefixWord, tailWord_888096, baseEnd_888096] using wordTrace_append hprefix tailTrace_888096
  have hstable : (prefixWord ++ tailWord_888096).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_888096).length < 2 ^ (prefixWord ++ tailWord_888096).sum := by decide
  have hdescent : baseEnd_888096 < baseStart_888096 := by decide
  rcases family_descends (prefixWord ++ tailWord_888096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_888245 : List Nat := [1, 3, 3, 2, 2, 2, 3, 1, 4]
def baseStart_888245 : Nat := 118140960795 + 888245 * 2 ^ 59
def prefixEnd_888245 : Nat := 4983230072969 + 3 ^ 40 * 888245 * 2
def baseEnd_888245 : Nat := 202709610645769987134463

theorem tailTrace_888245 : CollatzResearch.WordTrace tailWord_888245 prefixEnd_888245 202709610645769987134463 := by
  unfold tailWord_888245
  simp only [CollatzResearch.WordTrace]
  refine ⟨32396956667047540013642189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21597971111365026675761459 32396956667047540013642189)
  ·
    refine ⟨12148858750142827505115821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32396956667047540013642189 12148858750142827505115821)
    ·
      refine ⟨4555822031303560314418433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12148858750142827505115821 4555822031303560314418433)
      ·
        refine ⟨3416866523477670235813825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4555822031303560314418433 3416866523477670235813825)
        ·
          refine ⟨2562649892608252676860369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3416866523477670235813825 2562649892608252676860369)
          ·
            refine ⟨1921987419456189507645277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2562649892608252676860369 1921987419456189507645277)
            ·
              refine ⟨720745282296071065366979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1921987419456189507645277 720745282296071065366979)
              ·
                refine ⟨1081117923444106598050469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 720745282296071065366979 1081117923444106598050469)
                ·
                  refine ⟨202709610645769987134463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1081117923444106598050469 202709610645769987134463)
                  ·
                    rfl

theorem cell21_888245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 3, 1, 4].length) (baseStart_888245 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_888245 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_888245 prefixEnd_888245 := by exact prefixLift 888245
  have htrace : WordTrace (prefixWord ++ tailWord_888245) baseStart_888245 baseEnd_888245 := by
    simpa [prefixWord, tailWord_888245, baseEnd_888245] using wordTrace_append hprefix tailTrace_888245
  have hstable : (prefixWord ++ tailWord_888245).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_888245).length < 2 ^ (prefixWord ++ tailWord_888245).sum := by decide
  have hdescent : baseEnd_888245 < baseStart_888245 := by decide
  rcases family_descends (prefixWord ++ tailWord_888245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_888256 : List Nat := [2, 1, 1, 2, 3, 1, 4, 2, 5]
def baseStart_888256 : Nat := 118140960795 + 888256 * 2 ^ 59
def prefixEnd_888256 : Nat := 4983230072969 + 3 ^ 40 * 888256 * 2
def baseEnd_888256 : Nat := 202712120995636412451107

theorem tailTrace_888256 : CollatzResearch.WordTrace tailWord_888256 prefixEnd_888256 202712120995636412451107 := by
  unfold tailWord_888256
  simp only [CollatzResearch.WordTrace]
  refine ⟨16198678935003844446146311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21598238580005125928195081 16198678935003844446146311)
  ·
    refine ⟨24298018402505766669219467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16198678935003844446146311 24298018402505766669219467)
    ·
      refine ⟨36447027603758650003829201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24298018402505766669219467 36447027603758650003829201)
      ·
        refine ⟨27335270702818987502871901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36447027603758650003829201 27335270702818987502871901)
        ·
          refine ⟨10250726513557120313576963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27335270702818987502871901 10250726513557120313576963)
          ·
            refine ⟨15376089770335680470365445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10250726513557120313576963 15376089770335680470365445)
            ·
              refine ⟨2883016831937940088193521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15376089770335680470365445 2883016831937940088193521)
              ·
                refine ⟨2162262623953455066145141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2883016831937940088193521 2162262623953455066145141)
                ·
                  refine ⟨202712120995636412451107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2162262623953455066145141 202712120995636412451107)
                  ·
                    rfl

theorem cell21_888256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 4, 2, 5].length) (baseStart_888256 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_888256 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_888256 prefixEnd_888256 := by exact prefixLift 888256
  have htrace : WordTrace (prefixWord ++ tailWord_888256) baseStart_888256 baseEnd_888256 := by
    simpa [prefixWord, tailWord_888256, baseEnd_888256] using wordTrace_append hprefix tailTrace_888256
  have hstable : (prefixWord ++ tailWord_888256).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_888256).length < 2 ^ (prefixWord ++ tailWord_888256).sum := by decide
  have hdescent : baseEnd_888256 < baseStart_888256 := by decide
  rcases family_descends (prefixWord ++ tailWord_888256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_888287 : List Nat := [1, 1, 2, 3, 3, 1, 2, 4, 4]
def baseStart_888287 : Nat := 118140960795 + 888287 * 2 ^ 59
def prefixEnd_888287 : Nat := 4983230072969 + 3 ^ 40 * 888287 * 2
def baseEnd_888287 : Nat := 202719195617987247434377

theorem tailTrace_888287 : CollatzResearch.WordTrace tailWord_888287 prefixEnd_888287 202719195617987247434377 := by
  unfold tailWord_888287
  simp only [CollatzResearch.WordTrace]
  refine ⟨32398488532895381186671115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21598992355263587457780743 32398488532895381186671115)
  ·
    refine ⟨48597732799343071780006673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32398488532895381186671115 48597732799343071780006673)
    ·
      refine ⟨36448299599507303835005005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48597732799343071780006673 36448299599507303835005005)
      ·
        refine ⟨13668112349815238938126877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36448299599507303835005005 13668112349815238938126877)
        ·
          refine ⟨5125542131180714601797579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13668112349815238938126877 5125542131180714601797579)
          ·
            refine ⟨7688313196771071902696369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5125542131180714601797579 7688313196771071902696369)
            ·
              refine ⟨5766234897578303927022277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7688313196771071902696369 5766234897578303927022277)
              ·
                refine ⟨1081169043295931986316677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5766234897578303927022277 1081169043295931986316677)
                ·
                  refine ⟨202719195617987247434377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1081169043295931986316677 202719195617987247434377)
                  ·
                    rfl

theorem cell21_888287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 4, 4].length) (baseStart_888287 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_888287 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_888287 prefixEnd_888287 := by exact prefixLift 888287
  have htrace : WordTrace (prefixWord ++ tailWord_888287) baseStart_888287 baseEnd_888287 := by
    simpa [prefixWord, tailWord_888287, baseEnd_888287] using wordTrace_append hprefix tailTrace_888287
  have hstable : (prefixWord ++ tailWord_888287).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_888287).length < 2 ^ (prefixWord ++ tailWord_888287).sum := by decide
  have hdescent : baseEnd_888287 < baseStart_888287 := by decide
  rcases family_descends (prefixWord ++ tailWord_888287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_888304 : List Nat := [2, 1, 1, 1, 3, 4, 4, 1, 4]
def baseStart_888304 : Nat := 118140960795 + 888304 * 2 ^ 59
def prefixEnd_888304 : Nat := 4983230072969 + 3 ^ 40 * 888304 * 2
def baseEnd_888304 : Nat := 202723075249598995651009

theorem tailTrace_888304 : CollatzResearch.WordTrace tailWord_888304 prefixEnd_888304 202723075249598995651009 := by
  unfold tailWord_888304
  simp only [CollatzResearch.WordTrace]
  refine ⟨16199554286916896545019983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21599405715889195393359977 16199554286916896545019983)
  ·
    refine ⟨24299331430375344817529975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16199554286916896545019983 24299331430375344817529975)
    ·
      refine ⟨36448997145563017226294963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24299331430375344817529975 36448997145563017226294963)
      ·
        refine ⟨54673495718344525839442445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36448997145563017226294963 54673495718344525839442445)
        ·
          refine ⟨20502560894379197189790917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54673495718344525839442445 20502560894379197189790917)
          ·
            refine ⟨3844230167696099473085797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20502560894379197189790917 3844230167696099473085797)
            ·
              refine ⟨720793156443018651203587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3844230167696099473085797 720793156443018651203587)
              ·
                refine ⟨1081189734664527976805381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 720793156443018651203587 1081189734664527976805381)
                ·
                  refine ⟨202723075249598995651009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1081189734664527976805381 202723075249598995651009)
                  ·
                    rfl

theorem cell21_888304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 4, 1, 4].length) (baseStart_888304 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_888304 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_888304 prefixEnd_888304 := by exact prefixLift 888304
  have htrace : WordTrace (prefixWord ++ tailWord_888304) baseStart_888304 baseEnd_888304 := by
    simpa [prefixWord, tailWord_888304, baseEnd_888304] using wordTrace_append hprefix tailTrace_888304
  have hstable : (prefixWord ++ tailWord_888304).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_888304).length < 2 ^ (prefixWord ++ tailWord_888304).sum := by decide
  have hdescent : baseEnd_888304 < baseStart_888304 := by decide
  rcases family_descends (prefixWord ++ tailWord_888304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_888498 : List Nat := [3, 2, 1, 1, 1, 2, 2, 1, 8]
def baseStart_888498 : Nat := 118140960795 + 888498 * 2 ^ 59
def prefixEnd_888498 : Nat := 4983230072969 + 3 ^ 40 * 888498 * 2
def baseEnd_888498 : Nat := 202767348692697769417279

theorem tailTrace_888498 : CollatzResearch.WordTrace tailWord_888498 prefixEnd_888498 202767348692697769417279 := by
  unfold tailWord_888498
  simp only [CollatzResearch.WordTrace]
  refine ⟨8101546083782741055650537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21604122890087309481734765 8101546083782741055650537)
  ·
    refine ⟨6076159562837055791737903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8101546083782741055650537 6076159562837055791737903)
    ·
      refine ⟨9114239344255583687606855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6076159562837055791737903 9114239344255583687606855)
      ·
        refine ⟨13671359016383375531410283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9114239344255583687606855 13671359016383375531410283)
        ·
          refine ⟨20507038524575063297115425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13671359016383375531410283 20507038524575063297115425)
          ·
            refine ⟨15380278893431297472836569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20507038524575063297115425 15380278893431297472836569)
            ·
              refine ⟨11535209170073473104627427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15380278893431297472836569 11535209170073473104627427)
              ·
                refine ⟨17302813755110209656941141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11535209170073473104627427 17302813755110209656941141)
                ·
                  refine ⟨202767348692697769417279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 17302813755110209656941141 202767348692697769417279)
                  ·
                    rfl

theorem cell21_888498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 1, 8].length) (baseStart_888498 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_888498 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_888498 prefixEnd_888498 := by exact prefixLift 888498
  have htrace : WordTrace (prefixWord ++ tailWord_888498) baseStart_888498 baseEnd_888498 := by
    simpa [prefixWord, tailWord_888498, baseEnd_888498] using wordTrace_append hprefix tailTrace_888498
  have hstable : (prefixWord ++ tailWord_888498).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_888498).length < 2 ^ (prefixWord ++ tailWord_888498).sum := by decide
  have hdescent : baseEnd_888498 < baseStart_888498 := by decide
  rcases family_descends (prefixWord ++ tailWord_888498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_888529 : List Nat := [1, 2, 2, 1, 2, 4, 3, 6]
def baseStart_888529 : Nat := 118140960795 + 888529 * 2 ^ 59
def prefixEnd_888529 : Nat := 4983230072969 + 3 ^ 40 * 888529 * 2
def baseEnd_888529 : Nat := 67591474438349534800183

theorem tailTrace_888529 : CollatzResearch.WordTrace tailWord_888529 prefixEnd_888529 67591474438349534800183 := by
  unfold tailWord_888529
  simp only [CollatzResearch.WordTrace]
  refine ⟨32407314998018656516980641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21604876665345771011320427 32407314998018656516980641)
  ·
    refine ⟨24305486248513992387735481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32407314998018656516980641 24305486248513992387735481)
    ·
      refine ⟨18229114686385494290801611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24305486248513992387735481 18229114686385494290801611)
      ·
        refine ⟨27343672029578241436202417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18229114686385494290801611 27343672029578241436202417)
        ·
          refine ⟨20507754022183681077151813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27343672029578241436202417 20507754022183681077151813)
          ·
            refine ⟨3845203879159440201965965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20507754022183681077151813 3845203879159440201965965)
            ·
              refine ⟨1441951454684790075737237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3845203879159440201965965 1441951454684790075737237)
              ·
                refine ⟨67591474438349534800183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1441951454684790075737237 67591474438349534800183)
                ·
                  rfl

theorem cell21_888529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 3, 6].length) (baseStart_888529 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_888529 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_888529 prefixEnd_888529 := by exact prefixLift 888529
  have htrace : WordTrace (prefixWord ++ tailWord_888529) baseStart_888529 baseEnd_888529 := by
    simpa [prefixWord, tailWord_888529, baseEnd_888529] using wordTrace_append hprefix tailTrace_888529
  have hstable : (prefixWord ++ tailWord_888529).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_888529).length < 2 ^ (prefixWord ++ tailWord_888529).sum := by decide
  have hdescent : baseEnd_888529 < baseStart_888529 := by decide
  rcases family_descends (prefixWord ++ tailWord_888529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_888532 : List Nat := [2, 4, 1, 3, 1, 1, 2, 3, 4]
def baseStart_888532 : Nat := 118140960795 + 888532 * 2 ^ 59
def prefixEnd_888532 : Nat := 4983230072969 + 3 ^ 40 * 888532 * 2
def baseEnd_888532 : Nat := 202775107955921265850543

theorem tailTrace_888532 : CollatzResearch.WordTrace tailWord_888532 prefixEnd_888532 202775107955921265850543 := by
  unfold tailWord_888532
  simp only [CollatzResearch.WordTrace]
  refine ⟨16203712208503894014669925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21604949611338525352893233 16203712208503894014669925)
  ·
    refine ⟨3038196039094480127750611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16203712208503894014669925 3038196039094480127750611)
    ·
      refine ⟨4557294058641720191625917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3038196039094480127750611 4557294058641720191625917)
      ·
        refine ⟨1708985271990645071859719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4557294058641720191625917 1708985271990645071859719)
        ·
          refine ⟨2563477907985967607789579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1708985271990645071859719 2563477907985967607789579)
          ·
            refine ⟨3845216861978951411684369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2563477907985967607789579 3845216861978951411684369)
            ·
              refine ⟨2883912646484213558763277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3845216861978951411684369 2883912646484213558763277)
              ·
                refine ⟨1081467242431580084536229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2883912646484213558763277 1081467242431580084536229)
                ·
                  refine ⟨202775107955921265850543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1081467242431580084536229 202775107955921265850543)
                  ·
                    rfl

theorem cell21_888532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 2, 3, 4].length) (baseStart_888532 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_888532 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_888532 prefixEnd_888532 := by exact prefixLift 888532
  have htrace : WordTrace (prefixWord ++ tailWord_888532) baseStart_888532 baseEnd_888532 := by
    simpa [prefixWord, tailWord_888532, baseEnd_888532] using wordTrace_append hprefix tailTrace_888532
  have hstable : (prefixWord ++ tailWord_888532).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_888532).length < 2 ^ (prefixWord ++ tailWord_888532).sum := by decide
  have hdescent : baseEnd_888532 < baseStart_888532 := by decide
  rcases family_descends (prefixWord ++ tailWord_888532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_888577 : List Nat := [1, 2, 4, 1, 1, 1, 4, 4, 3]
def baseStart_888577 : Nat := 118140960795 + 888577 * 2 ^ 59
def prefixEnd_888577 : Nat := 4983230072969 + 3 ^ 40 * 888577 * 2
def baseEnd_888577 : Nat := 202785377569011187600451

theorem tailTrace_888577 : CollatzResearch.WordTrace tailWord_888577 prefixEnd_888577 202785377569011187600451 := by
  unfold tailWord_888577
  simp only [CollatzResearch.WordTrace]
  refine ⟨32409065701844760714727985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21606043801229840476485323 32409065701844760714727985)
  ·
    refine ⟨24306799276383570536045989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32409065701844760714727985 24306799276383570536045989)
    ·
      refine ⟨4557524864321919475508623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24306799276383570536045989 4557524864321919475508623)
      ·
        refine ⟨6836287296482879213262935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4557524864321919475508623 6836287296482879213262935)
        ·
          refine ⟨10254430944724318819894403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6836287296482879213262935 10254430944724318819894403)
          ·
            refine ⟨15381646417086478229841605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10254430944724318819894403 15381646417086478229841605)
            ·
              refine ⟨2884058703203714668095301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15381646417086478229841605 2884058703203714668095301)
              ·
                refine ⟨540761006850696500267869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2884058703203714668095301 540761006850696500267869)
                ·
                  refine ⟨202785377569011187600451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 540761006850696500267869 202785377569011187600451)
                  ·
                    rfl

theorem cell21_888577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 4, 4, 3].length) (baseStart_888577 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_888577 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_888577 prefixEnd_888577 := by exact prefixLift 888577
  have htrace : WordTrace (prefixWord ++ tailWord_888577) baseStart_888577 baseEnd_888577 := by
    simpa [prefixWord, tailWord_888577, baseEnd_888577] using wordTrace_append hprefix tailTrace_888577
  have hstable : (prefixWord ++ tailWord_888577).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_888577).length < 2 ^ (prefixWord ++ tailWord_888577).sum := by decide
  have hdescent : baseEnd_888577 < baseStart_888577 := by decide
  rcases family_descends (prefixWord ++ tailWord_888577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_888636 : List Nat := [2, 2, 2, 2, 1, 1, 5, 1, 5]
def baseStart_888636 : Nat := 118140960795 + 888636 * 2 ^ 59
def prefixEnd_888636 : Nat := 4983230072969 + 3 ^ 40 * 888636 * 2
def baseEnd_888636 : Nat := 202798842172840196116997

theorem tailTrace_888636 : CollatzResearch.WordTrace tailWord_888636 prefixEnd_888636 202798842172840196116997 := by
  unfold tailWord_888636
  simp only [CollatzResearch.WordTrace]
  refine ⟨16205608804315506895562881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21607478405754009194083841 16205608804315506895562881)
  ·
    refine ⟨12154206603236630171672161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16205608804315506895562881 12154206603236630171672161)
    ·
      refine ⟨9115654952427472628754121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12154206603236630171672161 9115654952427472628754121)
      ·
        refine ⟨6836741214320604471565591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9115654952427472628754121 6836741214320604471565591)
        ·
          refine ⟨10255111821480906707348387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6836741214320604471565591 10255111821480906707348387)
          ·
            refine ⟨15382667732221360061022581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10255111821480906707348387 15382667732221360061022581)
            ·
              refine ⟨1442125099895752505720867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15382667732221360061022581 1442125099895752505720867)
              ·
                refine ⟨2163187649843628758581301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1442125099895752505720867 2163187649843628758581301)
                ·
                  refine ⟨202798842172840196116997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2163187649843628758581301 202798842172840196116997)
                  ·
                    rfl

theorem cell21_888636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 5, 1, 5].length) (baseStart_888636 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_888636 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_888636 prefixEnd_888636 := by exact prefixLift 888636
  have htrace : WordTrace (prefixWord ++ tailWord_888636) baseStart_888636 baseEnd_888636 := by
    simpa [prefixWord, tailWord_888636, baseEnd_888636] using wordTrace_append hprefix tailTrace_888636
  have hstable : (prefixWord ++ tailWord_888636).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_888636).length < 2 ^ (prefixWord ++ tailWord_888636).sum := by decide
  have hdescent : baseEnd_888636 < baseStart_888636 := by decide
  rcases family_descends (prefixWord ++ tailWord_888636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_888743 : List Nat := [1, 1, 6, 1, 2, 2, 1, 1, 6]
def baseStart_888743 : Nat := 118140960795 + 888743 * 2 ^ 59
def prefixEnd_888743 : Nat := 4983230072969 + 3 ^ 40 * 888743 * 2
def baseEnd_888743 : Nat := 202823261030631787833445

theorem tailTrace_888743 : CollatzResearch.WordTrace tailWord_888743 prefixEnd_888743 202823261030631787833445 := by
  unfold tailWord_888743
  simp only [CollatzResearch.WordTrace]
  refine ⟨32415120219243371065270883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21610080146162247376847255 32415120219243371065270883)
  ·
    refine ⟨48622680328865056597906325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32415120219243371065270883 48622680328865056597906325)
    ·
      refine ⟨2279188140415549528026859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 48622680328865056597906325 2279188140415549528026859)
      ·
        refine ⟨3418782210623324292040289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2279188140415549528026859 3418782210623324292040289)
        ·
          refine ⟨2564086657967493219030217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3418782210623324292040289 2564086657967493219030217)
          ·
            refine ⟨1923064993475619914272663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2564086657967493219030217 1923064993475619914272663)
            ·
              refine ⟨2884597490213429871408995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1923064993475619914272663 2884597490213429871408995)
              ·
                refine ⟨4326896235320144807113493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2884597490213429871408995 4326896235320144807113493)
                ·
                  refine ⟨202823261030631787833445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4326896235320144807113493 202823261030631787833445)
                  ·
                    rfl

theorem cell21_888743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 1, 1, 6].length) (baseStart_888743 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_888743 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_888743 prefixEnd_888743 := by exact prefixLift 888743
  have htrace : WordTrace (prefixWord ++ tailWord_888743) baseStart_888743 baseEnd_888743 := by
    simpa [prefixWord, tailWord_888743, baseEnd_888743] using wordTrace_append hprefix tailTrace_888743
  have hstable : (prefixWord ++ tailWord_888743).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_888743).length < 2 ^ (prefixWord ++ tailWord_888743).sum := by decide
  have hdescent : baseEnd_888743 < baseStart_888743 := by decide
  rcases family_descends (prefixWord ++ tailWord_888743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_888816 : List Nat := [2, 1, 1, 1, 3, 2, 3, 8]
def baseStart_888816 : Nat := 118140960795 + 888816 * 2 ^ 59
def prefixEnd_888816 : Nat := 4983230072969 + 3 ^ 40 * 888816 * 2
def baseEnd_888816 : Nat := 67613306875066627705543

theorem tailTrace_888816 : CollatzResearch.WordTrace tailWord_888816 prefixEnd_888816 67613306875066627705543 := by
  unfold tailWord_888816
  simp only [CollatzResearch.WordTrace]
  refine ⟨16208891373989452266339151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21611855165319269688452201 16208891373989452266339151)
  ·
    refine ⟨24313337060984178399508727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16208891373989452266339151 24313337060984178399508727)
    ·
      refine ⟨36470005591476267599263091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24313337060984178399508727 36470005591476267599263091)
      ·
        refine ⟨54705008387214401398894637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36470005591476267599263091 54705008387214401398894637)
        ·
          refine ⟨20514378145205400524585489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54705008387214401398894637 20514378145205400524585489)
          ·
            refine ⟨15385783608904050393439117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20514378145205400524585489 15385783608904050393439117)
            ·
              refine ⟨5769668853339018897539669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15385783608904050393439117 5769668853339018897539669)
              ·
                refine ⟨67613306875066627705543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5769668853339018897539669 67613306875066627705543)
                ·
                  rfl

theorem cell21_888816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 8].length) (baseStart_888816 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_888816 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_888816 prefixEnd_888816 := by exact prefixLift 888816
  have htrace : WordTrace (prefixWord ++ tailWord_888816) baseStart_888816 baseEnd_888816 := by
    simpa [prefixWord, tailWord_888816, baseEnd_888816] using wordTrace_append hprefix tailTrace_888816
  have hstable : (prefixWord ++ tailWord_888816).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_888816).length < 2 ^ (prefixWord ++ tailWord_888816).sum := by decide
  have hdescent : baseEnd_888816 < baseStart_888816 := by decide
  rcases family_descends (prefixWord ++ tailWord_888816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_888909 : List Nat := [1, 6, 1, 1, 1, 1, 10]
def baseStart_888909 : Nat := 118140960795 + 888909 * 2 ^ 59
def prefixEnd_888909 : Nat := 4983230072969 + 3 ^ 40 * 888909 * 2
def baseEnd_888909 : Nat := 22540127165805820896271

theorem tailTrace_888909 : CollatzResearch.WordTrace tailWord_888909 prefixEnd_888909 22540127165805820896271 := by
  unfold tailWord_888909
  simp only [CollatzResearch.WordTrace]
  refine ⟨32421174736641981415813781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21614116491094654277209187 32421174736641981415813781)
  ·
    refine ⟨1519742565780092878866271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 32421174736641981415813781 1519742565780092878866271)
    ·
      refine ⟨2279613848670139318299407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1519742565780092878866271 2279613848670139318299407)
      ·
        refine ⟨3419420773005208977449111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2279613848670139318299407 3419420773005208977449111)
        ·
          refine ⟨5129131159507813466173667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3419420773005208977449111 5129131159507813466173667)
          ·
            refine ⟨7693696739261720199260501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5129131159507813466173667 7693696739261720199260501)
            ·
              refine ⟨22540127165805820896271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 7693696739261720199260501 22540127165805820896271)
              ·
                rfl

theorem cell21_888909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 10].length) (baseStart_888909 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_888909 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_888909 prefixEnd_888909 := by exact prefixLift 888909
  have htrace : WordTrace (prefixWord ++ tailWord_888909) baseStart_888909 baseEnd_888909 := by
    simpa [prefixWord, tailWord_888909, baseEnd_888909] using wordTrace_append hprefix tailTrace_888909
  have hstable : (prefixWord ++ tailWord_888909).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_888909).length < 2 ^ (prefixWord ++ tailWord_888909).sum := by decide
  have hdescent : baseEnd_888909 < baseStart_888909 := by decide
  rcases family_descends (prefixWord ++ tailWord_888909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_888957 : List Nat := [1, 4, 1, 1, 3, 2, 3, 3, 3]
def baseStart_888957 : Nat := 118140960795 + 888957 * 2 ^ 59
def prefixEnd_888957 : Nat := 4983230072969 + 3 ^ 40 * 888957 * 2
def baseEnd_888957 : Nat := 202872098746214971266341

theorem tailTrace_888957 : CollatzResearch.WordTrace tailWord_888957 prefixEnd_888957 202872098746214971266341 := by
  unfold tailWord_888957
  simp only [CollatzResearch.WordTrace]
  refine ⟨32422925440468085613561125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21615283626978723742374083 32422925440468085613561125)
  ·
    refine ⟨6079298520087766052542711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32422925440468085613561125 6079298520087766052542711)
    ·
      refine ⟨9118947780131649078814067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6079298520087766052542711 9118947780131649078814067)
      ·
        refine ⟨13678421670197473618221101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9118947780131649078814067 13678421670197473618221101)
        ·
          refine ⟨5129408126324052606832913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13678421670197473618221101 5129408126324052606832913)
          ·
            refine ⟨3847056094743039455124685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5129408126324052606832913 3847056094743039455124685)
            ·
              refine ⟨1442646035528639795671757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3847056094743039455124685 1442646035528639795671757)
              ·
                refine ⟨540992263323239923376909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1442646035528639795671757 540992263323239923376909)
                ·
                  refine ⟨202872098746214971266341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 540992263323239923376909 202872098746214971266341)
                  ·
                    rfl

theorem cell21_888957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 3, 3, 3].length) (baseStart_888957 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_888957 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_888957 prefixEnd_888957 := by exact prefixLift 888957
  have htrace : WordTrace (prefixWord ++ tailWord_888957) baseStart_888957 baseEnd_888957 := by
    simpa [prefixWord, tailWord_888957, baseEnd_888957] using wordTrace_append hprefix tailTrace_888957
  have hstable : (prefixWord ++ tailWord_888957).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_888957).length < 2 ^ (prefixWord ++ tailWord_888957).sum := by decide
  have hdescent : baseEnd_888957 < baseStart_888957 := by decide
  rcases family_descends (prefixWord ++ tailWord_888957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_888974 : List Nat := [4, 1, 1, 3, 4, 1, 1, 1, 5]
def baseStart_888974 : Nat := 118140960795 + 888974 * 2 ^ 59
def prefixEnd_888974 : Nat := 4983230072969 + 3 ^ 40 * 888974 * 2
def baseEnd_888974 : Nat := 202875978377826719482973

theorem tailTrace_888974 : CollatzResearch.WordTrace tailWord_888974 prefixEnd_888974 202875978377826719482973 := by
  unfold tailWord_888974
  simp only [CollatzResearch.WordTrace]
  refine ⟨4052943185175812189616247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21615696987604331677953317 4052943185175812189616247)
  ·
    refine ⟨6079414777763718284424371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4052943185175812189616247 6079414777763718284424371)
    ·
      refine ⟨9119122166645577426636557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6079414777763718284424371 9119122166645577426636557)
      ·
        refine ⟨3419670812492091534988709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9119122166645577426636557 3419670812492091534988709)
        ·
          refine ⟨641188277342267162810383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3419670812492091534988709 641188277342267162810383)
          ·
            refine ⟨961782416013400744215575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 641188277342267162810383 961782416013400744215575)
            ·
              refine ⟨1442673624020101116323363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 961782416013400744215575 1442673624020101116323363)
              ·
                refine ⟨2164010436030151674485045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1442673624020101116323363 2164010436030151674485045)
                ·
                  refine ⟨202875978377826719482973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2164010436030151674485045 202875978377826719482973)
                  ·
                    rfl

theorem cell21_888974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 1, 1, 5].length) (baseStart_888974 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_888974 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_888974 prefixEnd_888974 := by exact prefixLift 888974
  have htrace : WordTrace (prefixWord ++ tailWord_888974) baseStart_888974 baseEnd_888974 := by
    simpa [prefixWord, tailWord_888974, baseEnd_888974] using wordTrace_append hprefix tailTrace_888974
  have hstable : (prefixWord ++ tailWord_888974).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_888974).length < 2 ^ (prefixWord ++ tailWord_888974).sum := by decide
  have hdescent : baseEnd_888974 < baseStart_888974 := by decide
  rcases family_descends (prefixWord ++ tailWord_888974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_889016 : List Nat := [2, 1, 2, 1, 2, 1, 4, 5, 3]
def baseStart_889016 : Nat := 118140960795 + 889016 * 2 ^ 59
def prefixEnd_889016 : Nat := 4983230072969 + 3 ^ 40 * 889016 * 2
def baseEnd_889016 : Nat := 202885563350043979782887

theorem tailTrace_889016 : CollatzResearch.WordTrace tailWord_889016 prefixEnd_889016 202885563350043979782887 := by
  unfold tailWord_889016
  simp only [CollatzResearch.WordTrace]
  refine ⟨16212538673627169344979451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21616718231502892459972601 16212538673627169344979451)
  ·
    refine ⟨24318808010440754017469177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16212538673627169344979451 24318808010440754017469177)
    ·
      refine ⟨18239106007830565513101883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24318808010440754017469177 18239106007830565513101883)
      ·
        refine ⟨27358659011745848269652825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18239106007830565513101883 27358659011745848269652825)
        ·
          refine ⟨20518994258809386202239619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27358659011745848269652825 20518994258809386202239619)
          ·
            refine ⟨30778491388214079303359429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20518994258809386202239619 30778491388214079303359429)
            ·
              refine ⟨5770967135290139869379893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30778491388214079303359429 5770967135290139869379893)
              ·
                refine ⟨541028168933450612754365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5770967135290139869379893 541028168933450612754365)
                ·
                  refine ⟨202885563350043979782887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 541028168933450612754365 202885563350043979782887)
                  ·
                    rfl

theorem cell21_889016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 5, 3].length) (baseStart_889016 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_889016 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_889016 prefixEnd_889016 := by exact prefixLift 889016
  have htrace : WordTrace (prefixWord ++ tailWord_889016) baseStart_889016 baseEnd_889016 := by
    simpa [prefixWord, tailWord_889016, baseEnd_889016] using wordTrace_append hprefix tailTrace_889016
  have hstable : (prefixWord ++ tailWord_889016).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_889016).length < 2 ^ (prefixWord ++ tailWord_889016).sum := by decide
  have hdescent : baseEnd_889016 < baseStart_889016 := by decide
  rcases family_descends (prefixWord ++ tailWord_889016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_889137 : List Nat := [1, 2, 2, 3, 4, 2, 7]
def baseStart_889137 : Nat := 118140960795 + 889137 * 2 ^ 59
def prefixEnd_889137 : Nat := 4983230072969 + 3 ^ 40 * 889137 * 2
def baseEnd_889137 : Nat := 22545908577619406473997

theorem tailTrace_889137 : CollatzResearch.WordTrace tailWord_889137 prefixEnd_889137 22545908577619406473997 := by
  unfold tailWord_889137
  simp only [CollatzResearch.WordTrace]
  refine ⟨32429490579815976355113665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21619660386543984236742443 32429490579815976355113665)
  ·
    refine ⟨24322117934861982266335249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32429490579815976355113665 24322117934861982266335249)
    ·
      refine ⟨18241588451146486699751437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24322117934861982266335249 18241588451146486699751437)
      ·
        refine ⟨6840595669179932512406789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18241588451146486699751437 6840595669179932512406789)
        ·
          refine ⟨1282611687971237346076273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6840595669179932512406789 1282611687971237346076273)
          ·
            refine ⟨961958765978428009557205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1282611687971237346076273 961958765978428009557205)
            ·
              refine ⟨22545908577619406473997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 961958765978428009557205 22545908577619406473997)
              ·
                rfl

theorem cell21_889137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 7].length) (baseStart_889137 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_889137 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_889137 prefixEnd_889137 := by exact prefixLift 889137
  have htrace : WordTrace (prefixWord ++ tailWord_889137) baseStart_889137 baseEnd_889137 := by
    simpa [prefixWord, tailWord_889137, baseEnd_889137] using wordTrace_append hprefix tailTrace_889137
  have hstable : (prefixWord ++ tailWord_889137).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_889137).length < 2 ^ (prefixWord ++ tailWord_889137).sum := by decide
  have hdescent : baseEnd_889137 < baseStart_889137 := by decide
  rcases family_descends (prefixWord ++ tailWord_889137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_889196 : List Nat := [2, 2, 1, 1, 6, 9]
def baseStart_889196 : Nat := 118140960795 + 889196 * 2 ^ 59
def prefixEnd_889196 : Nat := 4983230072969 + 3 ^ 40 * 889196 * 2
def baseEnd_889196 : Nat := 7515801548237172843797

theorem tailTrace_889196 : CollatzResearch.WordTrace tailWord_889196 prefixEnd_889196 7515801548237172843797 := by
  unfold tailWord_889196
  simp only [CollatzResearch.WordTrace]
  refine ⟨16215821243301114715755721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21621094991068152954340961 16215821243301114715755721)
  ·
    refine ⟨12161865932475836036816791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16215821243301114715755721 12161865932475836036816791)
    ·
      refine ⟨18242798898713754055225187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12161865932475836036816791 18242798898713754055225187)
      ·
        refine ⟨27364198348070631082837781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18242798898713754055225187 27364198348070631082837781)
        ·
          refine ⟨1282696797565810832008021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 27364198348070631082837781 1282696797565810832008021)
          ·
            refine ⟨7515801548237172843797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1282696797565810832008021 7515801548237172843797)
            ·
              rfl

theorem cell21_889196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 9].length) (baseStart_889196 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_889196 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_889196 prefixEnd_889196 := by exact prefixLift 889196
  have htrace : WordTrace (prefixWord ++ tailWord_889196) baseStart_889196 baseEnd_889196 := by
    simpa [prefixWord, tailWord_889196, baseEnd_889196] using wordTrace_append hprefix tailTrace_889196
  have hstable : (prefixWord ++ tailWord_889196).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_889196).length < 2 ^ (prefixWord ++ tailWord_889196).sum := by decide
  have hdescent : baseEnd_889196 < baseStart_889196 := by decide
  rcases family_descends (prefixWord ++ tailWord_889196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_889202 : List Nat := [3, 2, 1, 2, 1, 5, 2, 2, 3]
def baseStart_889202 : Nat := 118140960795 + 889202 * 2 ^ 59
def prefixEnd_889202 : Nat := 4983230072969 + 3 ^ 40 * 889202 * 2
def baseEnd_889202 : Nat := 202928011084148989682507

theorem tailTrace_889202 : CollatzResearch.WordTrace tailWord_889202 prefixEnd_889202 202928011084148989682507 := by
  unfold tailWord_889202
  simp only [CollatzResearch.WordTrace]
  refine ⟨8107965331145123114057465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21621240883053661637486573 8107965331145123114057465)
  ·
    refine ⟨6080973998358842335543099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8107965331145123114057465 6080973998358842335543099)
    ·
      refine ⟨9121460997538263503314649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6080973998358842335543099 9121460997538263503314649)
      ·
        refine ⟨6841095748153697627485987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9121460997538263503314649 6841095748153697627485987)
        ·
          refine ⟨10261643622230546441228981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6841095748153697627485987 10261643622230546441228981)
          ·
            refine ⟨962029089584113728865217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10261643622230546441228981 962029089584113728865217)
            ·
              refine ⟨721521817188085296648913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 962029089584113728865217 721521817188085296648913)
              ·
                refine ⟨541141362891063972486685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 721521817188085296648913 541141362891063972486685)
                ·
                  refine ⟨202928011084148989682507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 541141362891063972486685 202928011084148989682507)
                  ·
                    rfl

theorem cell21_889202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 2, 2, 3].length) (baseStart_889202 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_889202 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_889202 prefixEnd_889202 := by exact prefixLift 889202
  have htrace : WordTrace (prefixWord ++ tailWord_889202) baseStart_889202 baseEnd_889202 := by
    simpa [prefixWord, tailWord_889202, baseEnd_889202] using wordTrace_append hprefix tailTrace_889202
  have hstable : (prefixWord ++ tailWord_889202).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_889202).length < 2 ^ (prefixWord ++ tailWord_889202).sum := by decide
  have hdescent : baseEnd_889202 < baseStart_889202 := by decide
  rcases family_descends (prefixWord ++ tailWord_889202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_889213 : List Nat := [1, 4, 1, 1, 2, 5, 1, 6]
def baseStart_889213 : Nat := 118140960795 + 889213 * 2 ^ 59
def prefixEnd_889213 : Nat := 4983230072969 + 3 ^ 40 * 889213 * 2
def baseEnd_889213 : Nat := 67643507144671804999717

theorem tailTrace_889213 : CollatzResearch.WordTrace tailWord_889213 prefixEnd_889213 67643507144671804999717 := by
  unfold tailWord_889213
  simp only [CollatzResearch.WordTrace]
  refine ⟨32432262527540641334880293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21621508351693760889920195 32432262527540641334880293)
  ·
    refine ⟨6081049223913870250290055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32432262527540641334880293 6081049223913870250290055)
    ·
      refine ⟨9121573835870805375435083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6081049223913870250290055 9121573835870805375435083)
      ·
        refine ⟨13682360753806208063152625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9121573835870805375435083 13682360753806208063152625)
        ·
          refine ⟨10261770565354656047364469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13682360753806208063152625 10261770565354656047364469)
          ·
            refine ⟨962040990501999004440419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10261770565354656047364469 962040990501999004440419)
            ·
              refine ⟨1443061485752998506660629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 962040990501999004440419 1443061485752998506660629)
              ·
                refine ⟨67643507144671804999717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1443061485752998506660629 67643507144671804999717)
                ·
                  rfl

theorem cell21_889213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 1, 6].length) (baseStart_889213 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_889213 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_889213 prefixEnd_889213 := by exact prefixLift 889213
  have htrace : WordTrace (prefixWord ++ tailWord_889213) baseStart_889213 baseEnd_889213 := by
    simpa [prefixWord, tailWord_889213, baseEnd_889213] using wordTrace_append hprefix tailTrace_889213
  have hstable : (prefixWord ++ tailWord_889213).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_889213).length < 2 ^ (prefixWord ++ tailWord_889213).sum := by decide
  have hdescent : baseEnd_889213 < baseStart_889213 := by decide
  rcases family_descends (prefixWord ++ tailWord_889213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_889227 : List Nat := [1, 1, 1, 1, 4, 5, 1, 2, 5]
def baseStart_889227 : Nat := 118140960795 + 889227 * 2 ^ 59
def prefixEnd_889227 : Nat := 4983230072969 + 3 ^ 40 * 889227 * 2
def baseEnd_889227 : Nat := 202933716424754501765789

theorem tailTrace_889227 : CollatzResearch.WordTrace tailWord_889227 prefixEnd_889227 202933716424754501765789 := by
  unfold tailWord_889227
  simp only [CollatzResearch.WordTrace]
  refine ⟨32432773149489921725889935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21621848766326614483926623 32432773149489921725889935)
  ·
    refine ⟨48649159724234882588834903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32432773149489921725889935 48649159724234882588834903)
    ·
      refine ⟨72973739586352323883252355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48649159724234882588834903 72973739586352323883252355)
      ·
        refine ⟨109460609379528485824878533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72973739586352323883252355 109460609379528485824878533)
        ·
          refine ⟨20523864258661591092164725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 109460609379528485824878533 20523864258661591092164725)
          ·
            refine ⟨1924112274249524164890443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 20523864258661591092164725 1924112274249524164890443)
            ·
              refine ⟨2886168411374286247335665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1924112274249524164890443 2886168411374286247335665)
              ·
                refine ⟨2164626308530714685501749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2886168411374286247335665 2164626308530714685501749)
                ·
                  refine ⟨202933716424754501765789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2164626308530714685501749 202933716424754501765789)
                  ·
                    rfl

theorem cell21_889227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 1, 2, 5].length) (baseStart_889227 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_889227 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_889227 prefixEnd_889227 := by exact prefixLift 889227
  have htrace : WordTrace (prefixWord ++ tailWord_889227) baseStart_889227 baseEnd_889227 := by
    simpa [prefixWord, tailWord_889227, baseEnd_889227] using wordTrace_append hprefix tailTrace_889227
  have hstable : (prefixWord ++ tailWord_889227).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_889227).length < 2 ^ (prefixWord ++ tailWord_889227).sum := by decide
  have hdescent : baseEnd_889227 < baseStart_889227 := by decide
  rcases family_descends (prefixWord ++ tailWord_889227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_889230 : List Nat := [4, 1, 1, 4, 1, 2, 3, 5]
def baseStart_889230 : Nat := 118140960795 + 889230 * 2 ^ 59
def prefixEnd_889230 : Nat := 4983230072969 + 3 ^ 40 * 889230 * 2
def baseEnd_889230 : Nat := 67644800355209054405261

theorem tailTrace_889230 : CollatzResearch.WordTrace tailWord_889230 prefixEnd_889230 67644800355209054405261 := by
  unfold tailWord_889230
  simp only [CollatzResearch.WordTrace]
  refine ⟨4054110321059881654781143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21621921712319368825499429 4054110321059881654781143)
  ·
    refine ⟨6081165481589822482171715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4054110321059881654781143 6081165481589822482171715)
    ·
      refine ⟨9121748222384733723257573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6081165481589822482171715 9121748222384733723257573)
      ·
        refine ⟨1710327791697137573110795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9121748222384733723257573 1710327791697137573110795)
        ·
          refine ⟨2565491687545706359666193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1710327791697137573110795 2565491687545706359666193)
          ·
            refine ⟨1924118765659279769749645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2565491687545706359666193 1924118765659279769749645)
            ·
              refine ⟨721544537122229913656117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1924118765659279769749645 721544537122229913656117)
              ·
                refine ⟨67644800355209054405261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 721544537122229913656117 67644800355209054405261)
                ·
                  rfl

theorem cell21_889230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 3, 5].length) (baseStart_889230 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_889230 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_889230 prefixEnd_889230 := by exact prefixLift 889230
  have htrace : WordTrace (prefixWord ++ tailWord_889230) baseStart_889230 baseEnd_889230 := by
    simpa [prefixWord, tailWord_889230, baseEnd_889230] using wordTrace_append hprefix tailTrace_889230
  have hstable : (prefixWord ++ tailWord_889230).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_889230).length < 2 ^ (prefixWord ++ tailWord_889230).sum := by decide
  have hdescent : baseEnd_889230 < baseStart_889230 := by decide
  rcases family_descends (prefixWord ++ tailWord_889230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_889241 : List Nat := [1, 2, 1, 2, 1, 4, 2, 2, 6]
def baseStart_889241 : Nat := 118140960795 + 889241 * 2 ^ 59
def prefixEnd_889241 : Nat := 4983230072969 + 3 ^ 40 * 889241 * 2
def baseEnd_889241 : Nat := 202936911415493588532427

theorem tailTrace_889241 : CollatzResearch.WordTrace tailWord_889241 prefixEnd_889241 202936911415493588532427 := by
  unfold tailWord_889241
  simp only [CollatzResearch.WordTrace]
  refine ⟨32433283771439202116899577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21622189180959468077933051 32433283771439202116899577)
  ·
    refine ⟨24324962828579401587674683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32433283771439202116899577 24324962828579401587674683)
    ·
      refine ⟨36487444242869102381512025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24324962828579401587674683 36487444242869102381512025)
      ·
        refine ⟨27365583182151826786134019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36487444242869102381512025 27365583182151826786134019)
        ·
          refine ⟨41048374773227740179201029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27365583182151826786134019 41048374773227740179201029)
          ·
            refine ⟨7696570269980201283600193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41048374773227740179201029 7696570269980201283600193)
            ·
              refine ⟨5772427702485150962700145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7696570269980201283600193 5772427702485150962700145)
              ·
                refine ⟨4329320776863863222025109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5772427702485150962700145 4329320776863863222025109)
                ·
                  refine ⟨202936911415493588532427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4329320776863863222025109 202936911415493588532427)
                  ·
                    rfl

theorem cell21_889241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 2, 6].length) (baseStart_889241 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_889241 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_889241 prefixEnd_889241 := by exact prefixLift 889241
  have htrace : WordTrace (prefixWord ++ tailWord_889241) baseStart_889241 baseEnd_889241 := by
    simpa [prefixWord, tailWord_889241, baseEnd_889241] using wordTrace_append hprefix tailTrace_889241
  have hstable : (prefixWord ++ tailWord_889241).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_889241).length < 2 ^ (prefixWord ++ tailWord_889241).sum := by decide
  have hdescent : baseEnd_889241 < baseStart_889241 := by decide
  rcases family_descends (prefixWord ++ tailWord_889241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_889261 : List Nat := [1, 5, 2, 2, 2, 1, 2, 1, 5]
def baseStart_889261 : Nat := 118140960795 + 889261 * 2 ^ 59
def prefixEnd_889261 : Nat := 4983230072969 + 3 ^ 40 * 889261 * 2
def baseEnd_889261 : Nat := 202941475687977998199053

theorem tailTrace_889261 : CollatzResearch.WordTrace tailWord_889261 prefixEnd_889261 202941475687977998199053 := by
  unfold tailWord_889261
  simp only [CollatzResearch.WordTrace]
  refine ⟨32434013231366745532627637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21622675487577830355085091 32434013231366745532627637)
  ·
    refine ⟨3040688740440632393683841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 32434013231366745532627637 3040688740440632393683841)
    ·
      refine ⟨2280516555330474295262881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3040688740440632393683841 2280516555330474295262881)
      ·
        refine ⟨1710387416497855721447161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2280516555330474295262881 1710387416497855721447161)
        ·
          refine ⟨1282790562373391791085371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1710387416497855721447161 1282790562373391791085371)
          ·
            refine ⟨1924185843560087686628057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1282790562373391791085371 1924185843560087686628057)
            ·
              refine ⟨1443139382670065764971043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1924185843560087686628057 1443139382670065764971043)
              ·
                refine ⟨2164709074005098647456565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1443139382670065764971043 2164709074005098647456565)
                ·
                  refine ⟨202941475687977998199053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2164709074005098647456565 202941475687977998199053)
                  ·
                    rfl

theorem cell21_889261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 2, 1, 5].length) (baseStart_889261 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_889261 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_889261 prefixEnd_889261 := by exact prefixLift 889261
  have htrace : WordTrace (prefixWord ++ tailWord_889261) baseStart_889261 baseEnd_889261 := by
    simpa [prefixWord, tailWord_889261, baseEnd_889261] using wordTrace_append hprefix tailTrace_889261
  have hstable : (prefixWord ++ tailWord_889261).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_889261).length < 2 ^ (prefixWord ++ tailWord_889261).sum := by decide
  have hdescent : baseEnd_889261 < baseStart_889261 := by decide
  rcases family_descends (prefixWord ++ tailWord_889261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_889281 : List Nat := [1, 2, 7, 1, 2, 1, 2, 5]
def baseStart_889281 : Nat := 118140960795 + 889281 * 2 ^ 59
def prefixEnd_889281 : Nat := 4983230072969 + 3 ^ 40 * 889281 * 2
def baseEnd_889281 : Nat := 67648679986820802621893

theorem tailTrace_889281 : CollatzResearch.WordTrace tailWord_889281 prefixEnd_889281 67648679986820802621893 := by
  unfold tailWord_889281
  simp only [CollatzResearch.WordTrace]
  refine ⟨32434742691294288948355697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21623161794196192632237131 32434742691294288948355697)
  ·
    refine ⟨24326057018470716711266773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32434742691294288948355697 24326057018470716711266773)
    ·
      refine ⟨570141961370407422920315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 24326057018470716711266773 570141961370407422920315)
      ·
        refine ⟨855212942055611134380473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 570141961370407422920315 855212942055611134380473)
        ·
          refine ⟨641409706541708350785355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 855212942055611134380473 641409706541708350785355)
          ·
            refine ⟨962114559812562526178033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 641409706541708350785355 962114559812562526178033)
            ·
              refine ⟨721585919859421894633525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 962114559812562526178033 721585919859421894633525)
              ·
                refine ⟨67648679986820802621893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 721585919859421894633525 67648679986820802621893)
                ·
                  rfl

theorem cell21_889281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 2, 5].length) (baseStart_889281 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_889281 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_889281 prefixEnd_889281 := by exact prefixLift 889281
  have htrace : WordTrace (prefixWord ++ tailWord_889281) baseStart_889281 baseEnd_889281 := by
    simpa [prefixWord, tailWord_889281, baseEnd_889281] using wordTrace_append hprefix tailTrace_889281
  have hstable : (prefixWord ++ tailWord_889281).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_889281).length < 2 ^ (prefixWord ++ tailWord_889281).sum := by decide
  have hdescent : baseEnd_889281 < baseStart_889281 := by decide
  rcases family_descends (prefixWord ++ tailWord_889281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_889320 : List Nat := [2, 1, 4, 1, 1, 5, 1, 1, 5]
def baseStart_889320 : Nat := 118140960795 + 889320 * 2 ^ 59
def prefixEnd_889320 : Nat := 4983230072969 + 3 ^ 40 * 889320 * 2
def baseEnd_889320 : Nat := 202954940291807006715599

theorem tailTrace_889320 : CollatzResearch.WordTrace tailWord_889320 prefixEnd_889320 202954940291807006715599 := by
  unfold tailWord_889320
  simp only [CollatzResearch.WordTrace]
  refine ⟨16218082569076499304512707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21624110092101999072683609 16218082569076499304512707)
  ·
    refine ⟨24327123853614748956769061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16218082569076499304512707 24327123853614748956769061)
    ·
      refine ⟨4561335722552765429394199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24327123853614748956769061 4561335722552765429394199)
      ·
        refine ⟨6842003583829148144091299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4561335722552765429394199 6842003583829148144091299)
        ·
          refine ⟨10263005375743722216136949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6842003583829148144091299 10263005375743722216136949)
          ·
            refine ⟨962156753975973957762839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10263005375743722216136949 962156753975973957762839)
            ·
              refine ⟨1443235130963960936644259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 962156753975973957762839 1443235130963960936644259)
              ·
                refine ⟨2164852696445941404966389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1443235130963960936644259 2164852696445941404966389)
                ·
                  refine ⟨202954940291807006715599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2164852696445941404966389 202954940291807006715599)
                  ·
                    rfl

theorem cell21_889320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 1, 1, 5].length) (baseStart_889320 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_889320 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_889320 prefixEnd_889320 := by exact prefixLift 889320
  have htrace : WordTrace (prefixWord ++ tailWord_889320) baseStart_889320 baseEnd_889320 := by
    simpa [prefixWord, tailWord_889320, baseEnd_889320] using wordTrace_append hprefix tailTrace_889320
  have hstable : (prefixWord ++ tailWord_889320).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_889320).length < 2 ^ (prefixWord ++ tailWord_889320).sum := by decide
  have hdescent : baseEnd_889320 < baseStart_889320 := by decide
  rcases family_descends (prefixWord ++ tailWord_889320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_889458 : List Nat := [3, 2, 1, 2, 4, 2, 2, 5]
def baseStart_889458 : Nat := 118140960795 + 889458 * 2 ^ 59
def prefixEnd_889458 : Nat := 4983230072969 + 3 ^ 40 * 889458 * 2
def baseEnd_889458 : Nat := 67662144590649811138439

theorem tailTrace_889458 : CollatzResearch.WordTrace tailWord_889458 prefixEnd_889458 67662144590649811138439 := by
  unfold tailWord_889458
  simp only [CollatzResearch.WordTrace]
  refine ⟨8110299602913262044387257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21627465607768698785032685 8110299602913262044387257)
  ·
    refine ⟨6082724702184946533290443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8110299602913262044387257 6082724702184946533290443)
    ·
      refine ⟨9124087053277419799935665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6082724702184946533290443 9124087053277419799935665)
      ·
        refine ⟨6843065289958064849951749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9124087053277419799935665 6843065289958064849951749)
        ·
          refine ⟨1283074741867137159365953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6843065289958064849951749 1283074741867137159365953)
          ·
            refine ⟨962306056400352869524465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1283074741867137159365953 962306056400352869524465)
            ·
              refine ⟨721729542300264652143349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 962306056400352869524465 721729542300264652143349)
              ·
                refine ⟨67662144590649811138439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 721729542300264652143349 67662144590649811138439)
                ·
                  rfl

theorem cell21_889458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 2, 5].length) (baseStart_889458 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_889458 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_889458 prefixEnd_889458 := by exact prefixLift 889458
  have htrace : WordTrace (prefixWord ++ tailWord_889458) baseStart_889458 baseEnd_889458 := by
    simpa [prefixWord, tailWord_889458, baseEnd_889458] using wordTrace_append hprefix tailTrace_889458
  have hstable : (prefixWord ++ tailWord_889458).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_889458).length < 2 ^ (prefixWord ++ tailWord_889458).sum := by decide
  have hdescent : baseEnd_889458 < baseStart_889458 := by decide
  rcases family_descends (prefixWord ++ tailWord_889458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_889472 : List Nat := [2, 1, 1, 2, 1, 5, 3, 3, 3]
def baseStart_889472 : Nat := 118140960795 + 889472 * 2 ^ 59
def prefixEnd_889472 : Nat := 4983230072969 + 3 ^ 40 * 889472 * 2
def baseEnd_889472 : Nat := 202989628762688520181955

theorem tailTrace_889472 : CollatzResearch.WordTrace tailWord_889472 prefixEnd_889472 202989628762688520181955 := by
  unfold tailWord_889472
  simp only [CollatzResearch.WordTrace]
  refine ⟨16220854516801164284279335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21627806022401552379039113 16220854516801164284279335)
  ·
    refine ⟨24331281775201746426419003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16220854516801164284279335 24331281775201746426419003)
    ·
      refine ⟨36496922662802619639628505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24331281775201746426419003 36496922662802619639628505)
      ·
        refine ⟨27372691997101964729721379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36496922662802619639628505 27372691997101964729721379)
        ·
          refine ⟨41059037995652947094582069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27372691997101964729721379 41059037995652947094582069)
          ·
            refine ⟨3849284812092463790117069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 41059037995652947094582069 3849284812092463790117069)
            ·
              refine ⟨1443481804534673921293901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3849284812092463790117069 1443481804534673921293901)
              ·
                refine ⟨541305676700502720485213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1443481804534673921293901 541305676700502720485213)
                ·
                  refine ⟨202989628762688520181955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 541305676700502720485213 202989628762688520181955)
                  ·
                    rfl

theorem cell21_889472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 3, 3, 3].length) (baseStart_889472 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_889472 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_889472 prefixEnd_889472 := by exact prefixLift 889472
  have htrace : WordTrace (prefixWord ++ tailWord_889472) baseStart_889472 baseEnd_889472 := by
    simpa [prefixWord, tailWord_889472, baseEnd_889472] using wordTrace_append hprefix tailTrace_889472
  have hstable : (prefixWord ++ tailWord_889472).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_889472).length < 2 ^ (prefixWord ++ tailWord_889472).sum := by decide
  have hdescent : baseEnd_889472 < baseStart_889472 := by decide
  rcases family_descends (prefixWord ++ tailWord_889472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_889486 : List Nat := [4, 1, 1, 3, 1, 1, 2, 4, 4]
def baseStart_889486 : Nat := 118140960795 + 889486 * 2 ^ 59
def prefixEnd_889486 : Nat := 4983230072969 + 3 ^ 40 * 889486 * 2
def baseEnd_889486 : Nat := 202992823753427606948593

theorem tailTrace_889486 : CollatzResearch.WordTrace tailWord_889486 prefixEnd_889486 202992823753427606948593 := by
  unfold tailWord_889486
  simp only [CollatzResearch.WordTrace]
  refine ⟨4055277456943951119946039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21628146437034405973045541 4055277456943951119946039)
  ·
    refine ⟨6082916185415926679919059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4055277456943951119946039 6082916185415926679919059)
    ·
      refine ⟨9124374278123890019878589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6082916185415926679919059 9124374278123890019878589)
      ·
        refine ⟨3421640354296458757454471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9124374278123890019878589 3421640354296458757454471)
        ·
          refine ⟨5132460531444688136181707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3421640354296458757454471 5132460531444688136181707)
          ·
            refine ⟨7698690797167032204272561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5132460531444688136181707 7698690797167032204272561)
            ·
              refine ⟨5774018097875274153204421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7698690797167032204272561 5774018097875274153204421)
              ·
                refine ⟨1082628393351613903725829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5774018097875274153204421 1082628393351613903725829)
                ·
                  refine ⟨202992823753427606948593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1082628393351613903725829 202992823753427606948593)
                  ·
                    rfl

theorem cell21_889486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 4, 4].length) (baseStart_889486 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_889486 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_889486 prefixEnd_889486 := by exact prefixLift 889486
  have htrace : WordTrace (prefixWord ++ tailWord_889486) baseStart_889486 baseEnd_889486 := by
    simpa [prefixWord, tailWord_889486, baseEnd_889486] using wordTrace_append hprefix tailTrace_889486
  have hstable : (prefixWord ++ tailWord_889486).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_889486).length < 2 ^ (prefixWord ++ tailWord_889486).sum := by decide
  have hdescent : baseEnd_889486 < baseStart_889486 := by decide
  rcases family_descends (prefixWord ++ tailWord_889486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_889500 : List Nat := [2, 2, 3, 2, 2, 1, 1, 8]
def baseStart_889500 : Nat := 118140960795 + 889500 * 2 ^ 59
def prefixEnd_889500 : Nat := 4983230072969 + 3 ^ 40 * 889500 * 2
def baseEnd_889500 : Nat := 67665339581388897905077

theorem tailTrace_889500 : CollatzResearch.WordTrace tailWord_889500 prefixEnd_889500 67665339581388897905077 := by
  unfold tailWord_889500
  simp only [CollatzResearch.WordTrace]
  refine ⟨16221365138750444675288977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21628486851667259567051969 16221365138750444675288977)
  ·
    refine ⟨12166023854062833506466733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16221365138750444675288977 12166023854062833506466733)
    ·
      refine ⟨4562258945273562564925025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12166023854062833506466733 4562258945273562564925025)
      ·
        refine ⟨3421694208955171923693769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4562258945273562564925025 3421694208955171923693769)
        ·
          refine ⟨2566270656716378942770327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3421694208955171923693769 2566270656716378942770327)
          ·
            refine ⟨3849405985074568414155491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2566270656716378942770327 3849405985074568414155491)
            ·
              refine ⟨5774108977611852621233237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3849405985074568414155491 5774108977611852621233237)
              ·
                refine ⟨67665339581388897905077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5774108977611852621233237 67665339581388897905077)
                ·
                  rfl

theorem cell21_889500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 8].length) (baseStart_889500 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_889500 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_889500 prefixEnd_889500 := by exact prefixLift 889500
  have htrace : WordTrace (prefixWord ++ tailWord_889500) baseStart_889500 baseEnd_889500 := by
    simpa [prefixWord, tailWord_889500, baseEnd_889500] using wordTrace_append hprefix tailTrace_889500
  have hstable : (prefixWord ++ tailWord_889500).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_889500).length < 2 ^ (prefixWord ++ tailWord_889500).sum := by decide
  have hdescent : baseEnd_889500 < baseStart_889500 := by decide
  rcases family_descends (prefixWord ++ tailWord_889500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_889607 : List Nat := [1, 1, 4, 4, 1, 1, 1, 3, 5]
def baseStart_889607 : Nat := 118140960795 + 889607 * 2 ^ 59
def prefixEnd_889607 : Nat := 4983230072969 + 3 ^ 40 * 889607 * 2
def baseEnd_889607 : Nat := 203020437601958285431679

theorem tailTrace_889607 : CollatzResearch.WordTrace tailWord_889607 prefixEnd_889607 203020437601958285431679 := by
  unfold tailWord_889607
  simp only [CollatzResearch.WordTrace]
  refine ⟨32446632888113246624723075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21631088592075497749815383 32446632888113246624723075)
  ·
    refine ⟨48669949332169869937084613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32446632888113246624723075 48669949332169869937084613)
    ·
      refine ⟨9125615499781850613203365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48669949332169869937084613 9125615499781850613203365)
      ·
        refine ⟨1711052906209096989975631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9125615499781850613203365 1711052906209096989975631)
        ·
          refine ⟨2566579359313645484963447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1711052906209096989975631 2566579359313645484963447)
          ·
            refine ⟨3849869038970468227445171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2566579359313645484963447 3849869038970468227445171)
            ·
              refine ⟨5774803558455702341167757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3849869038970468227445171 5774803558455702341167757)
              ·
                refine ⟨2165551334420888377937909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5774803558455702341167757 2165551334420888377937909)
                ·
                  refine ⟨203020437601958285431679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2165551334420888377937909 203020437601958285431679)
                  ·
                    rfl

theorem cell21_889607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 3, 5].length) (baseStart_889607 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_889607 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_889607 prefixEnd_889607 := by exact prefixLift 889607
  have htrace : WordTrace (prefixWord ++ tailWord_889607) baseStart_889607 baseEnd_889607 := by
    simpa [prefixWord, tailWord_889607, baseEnd_889607] using wordTrace_append hprefix tailTrace_889607
  have hstable : (prefixWord ++ tailWord_889607).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_889607).length < 2 ^ (prefixWord ++ tailWord_889607).sum := by decide
  have hdescent : baseEnd_889607 < baseStart_889607 := by decide
  rcases family_descends (prefixWord ++ tailWord_889607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_889717 : List Nat := [1, 3, 4, 1, 1, 2, 4, 2, 3]
def baseStart_889717 : Nat := 118140960795 + 889717 * 2 ^ 59
def prefixEnd_889717 : Nat := 4983230072969 + 3 ^ 40 * 889717 * 2
def baseEnd_889717 : Nat := 203045541100622538598121

theorem tailTrace_889717 : CollatzResearch.WordTrace tailWord_889717 prefixEnd_889717 203045541100622538598121 := by
  unfold tailWord_889717
  simp only [CollatzResearch.WordTrace]
  refine ⟨32450644917714735411227405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21633763278476490274151603 32450644917714735411227405)
  ·
    refine ⟨12168991844143025779210277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32450644917714735411227405 12168991844143025779210277)
    ·
      refine ⟨2281685970776817333601927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12168991844143025779210277 2281685970776817333601927)
      ·
        refine ⟨3422528956165226000402891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2281685970776817333601927 3422528956165226000402891)
        ·
          refine ⟨5133793434247839000604337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3422528956165226000402891 5133793434247839000604337)
          ·
            refine ⟨3850345075685879250453253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5133793434247839000604337 3850345075685879250453253)
            ·
              refine ⟨721939701691102359459985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3850345075685879250453253 721939701691102359459985)
              ·
                refine ⟨541454776268326769594989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 721939701691102359459985 541454776268326769594989)
                ·
                  refine ⟨203045541100622538598121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 541454776268326769594989 203045541100622538598121)
                  ·
                    rfl

theorem cell21_889717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 4, 2, 3].length) (baseStart_889717 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_889717 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_889717 prefixEnd_889717 := by exact prefixLift 889717
  have htrace : WordTrace (prefixWord ++ tailWord_889717) baseStart_889717 baseEnd_889717 := by
    simpa [prefixWord, tailWord_889717, baseEnd_889717] using wordTrace_append hprefix tailTrace_889717
  have hstable : (prefixWord ++ tailWord_889717).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_889717).length < 2 ^ (prefixWord ++ tailWord_889717).sum := by decide
  have hdescent : baseEnd_889717 < baseStart_889717 := by decide
  rcases family_descends (prefixWord ++ tailWord_889717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_889782 : List Nat := [5, 1, 4, 1, 1, 1, 3, 1, 4]
def baseStart_889782 : Nat := 118140960795 + 889782 * 2 ^ 59
def prefixEnd_889782 : Nat := 4983230072969 + 3 ^ 40 * 889782 * 2
def baseEnd_889782 : Nat := 203060374986196870014655

theorem tailTrace_889782 : CollatzResearch.WordTrace tailWord_889782 prefixEnd_889782 203060374986196870014655 := by
  unfold tailWord_889782
  simp only [CollatzResearch.WordTrace]
  refine ⟨2028313478904953219521475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21635343774986167674895733 2028313478904953219521475)
  ·
    refine ⟨3042470218357429829282213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2028313478904953219521475 3042470218357429829282213)
    ·
      refine ⟨570463165942018092990415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3042470218357429829282213 570463165942018092990415)
      ·
        refine ⟨855694748913027139485623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 570463165942018092990415 855694748913027139485623)
        ·
          refine ⟨1283542123369540709228435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 855694748913027139485623 1283542123369540709228435)
          ·
            refine ⟨1925313185054311063842653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1283542123369540709228435 1925313185054311063842653)
            ·
              refine ⟨721992444395366648940995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1925313185054311063842653 721992444395366648940995)
              ·
                refine ⟨1082988666593049973411493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 721992444395366648940995 1082988666593049973411493)
                ·
                  refine ⟨203060374986196870014655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1082988666593049973411493 203060374986196870014655)
                  ·
                    rfl

theorem cell21_889782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 3, 1, 4].length) (baseStart_889782 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_889782 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_889782 prefixEnd_889782 := by exact prefixLift 889782
  have htrace : WordTrace (prefixWord ++ tailWord_889782) baseStart_889782 baseEnd_889782 := by
    simpa [prefixWord, tailWord_889782, baseEnd_889782] using wordTrace_append hprefix tailTrace_889782
  have hstable : (prefixWord ++ tailWord_889782).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_889782).length < 2 ^ (prefixWord ++ tailWord_889782).sum := by decide
  have hdescent : baseEnd_889782 < baseStart_889782 := by decide
  rcases family_descends (prefixWord ++ tailWord_889782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_889849 : List Nat := [1, 2, 1, 3, 1, 3, 3, 3, 4]
def baseStart_889849 : Nat := 118140960795 + 889849 * 2 ^ 59
def prefixEnd_889849 : Nat := 4983230072969 + 3 ^ 40 * 889849 * 2
def baseEnd_889849 : Nat := 203075665299019642397851

theorem tailTrace_889849 : CollatzResearch.WordTrace tailWord_889849 prefixEnd_889849 203075665299019642397851 := by
  unfold tailWord_889849
  simp only [CollatzResearch.WordTrace]
  refine ⟨32455459353236521955032601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21636972902157681303355067 32455459353236521955032601)
  ·
    refine ⟨24341594514927391466274451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32455459353236521955032601 24341594514927391466274451)
    ·
      refine ⟨36512391772391087199411677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24341594514927391466274451 36512391772391087199411677)
      ·
        refine ⟨13692146914646657699779379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36512391772391087199411677 13692146914646657699779379)
        ·
          refine ⟨20538220371969986549669069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13692146914646657699779379 20538220371969986549669069)
          ·
            refine ⟨7701832639488744956125901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20538220371969986549669069 7701832639488744956125901)
            ·
              refine ⟨2888187239808279358547213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7701832639488744956125901 2888187239808279358547213)
              ·
                refine ⟨1083070214928104759455205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2888187239808279358547213 1083070214928104759455205)
                ·
                  refine ⟨203075665299019642397851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1083070214928104759455205 203075665299019642397851)
                  ·
                    rfl

theorem cell21_889849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 3, 3, 4].length) (baseStart_889849 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_889849 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_889849 prefixEnd_889849 := by exact prefixLift 889849
  have htrace : WordTrace (prefixWord ++ tailWord_889849) baseStart_889849 baseEnd_889849 := by
    simpa [prefixWord, tailWord_889849, baseEnd_889849] using wordTrace_append hprefix tailTrace_889849
  have hstable : (prefixWord ++ tailWord_889849).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_889849).length < 2 ^ (prefixWord ++ tailWord_889849).sum := by decide
  have hdescent : baseEnd_889849 < baseStart_889849 := by decide
  rcases family_descends (prefixWord ++ tailWord_889849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_889863 : List Nat := [1, 1, 4, 3, 1, 1, 1, 9]
def baseStart_889863 : Nat := 118140960795 + 889863 * 2 ^ 59
def prefixEnd_889863 : Nat := 4983230072969 + 3 ^ 40 * 889863 * 2
def baseEnd_889863 : Nat := 67692953429919576388163

theorem tailTrace_889863 : CollatzResearch.WordTrace tailWord_889863 prefixEnd_889863 67692953429919576388163 := by
  unfold tailWord_889863
  simp only [CollatzResearch.WordTrace]
  refine ⟨32455969975185802346042243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21637313316790534897361495 32455969975185802346042243)
  ·
    refine ⟨48683954962778703519063365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32455969975185802346042243 48683954962778703519063365)
    ·
      refine ⟨9128241555521006909824381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48683954962778703519063365 9128241555521006909824381)
      ·
        refine ⟨3423090583320377591184143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9128241555521006909824381 3423090583320377591184143)
        ·
          refine ⟨5134635874980566386776215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3423090583320377591184143 5134635874980566386776215)
          ·
            refine ⟨7701953812470849580164323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5134635874980566386776215 7701953812470849580164323)
            ·
              refine ⟨11552930718706274370246485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7701953812470849580164323 11552930718706274370246485)
              ·
                refine ⟨67692953429919576388163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 11552930718706274370246485 67692953429919576388163)
                ·
                  rfl

theorem cell21_889863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 9].length) (baseStart_889863 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_889863 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_889863 prefixEnd_889863 := by exact prefixLift 889863
  have htrace : WordTrace (prefixWord ++ tailWord_889863) baseStart_889863 baseEnd_889863 := by
    simpa [prefixWord, tailWord_889863, baseEnd_889863] using wordTrace_append hprefix tailTrace_889863
  have hstable : (prefixWord ++ tailWord_889863).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_889863).length < 2 ^ (prefixWord ++ tailWord_889863).sum := by decide
  have hdescent : baseEnd_889863 < baseStart_889863 := by decide
  rcases family_descends (prefixWord ++ tailWord_889863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_889970 : List Nat := [3, 2, 1, 2, 2, 1, 1, 4, 5]
def baseStart_889970 : Nat := 118140960795 + 889970 * 2 ^ 59
def prefixEnd_889970 : Nat := 4983230072969 + 3 ^ 40 * 889970 * 2
def baseEnd_889970 : Nat := 203103279147550320880937

theorem tailTrace_889970 : CollatzResearch.WordTrace tailWord_889970 prefixEnd_889970 203103279147550320880937 := by
  unfold tailWord_889970
  simp only [CollatzResearch.WordTrace]
  refine ⟨8114968146449539905046841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21639915057198773080124909 8114968146449539905046841)
  ·
    refine ⟨6086226109837154928785131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8114968146449539905046841 6086226109837154928785131)
    ·
      refine ⟨9129339164755732393177697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6086226109837154928785131 9129339164755732393177697)
      ·
        refine ⟨6847004373566799294883273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9129339164755732393177697 6847004373566799294883273)
        ·
          refine ⟨5135253280175099471162455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6847004373566799294883273 5135253280175099471162455)
          ·
            refine ⟨7702879920262649206743683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5135253280175099471162455 7702879920262649206743683)
            ·
              refine ⟨11554319880393973810115525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7702879920262649206743683 11554319880393973810115525)
              ·
                refine ⟨2166434977573870089396661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11554319880393973810115525 2166434977573870089396661)
                ·
                  refine ⟨203103279147550320880937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2166434977573870089396661 203103279147550320880937)
                  ·
                    rfl

theorem cell21_889970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 4, 5].length) (baseStart_889970 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_889970 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_889970 prefixEnd_889970 := by exact prefixLift 889970
  have htrace : WordTrace (prefixWord ++ tailWord_889970) baseStart_889970 baseEnd_889970 := by
    simpa [prefixWord, tailWord_889970, baseEnd_889970] using wordTrace_append hprefix tailTrace_889970
  have hstable : (prefixWord ++ tailWord_889970).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_889970).length < 2 ^ (prefixWord ++ tailWord_889970).sum := by decide
  have hdescent : baseEnd_889970 < baseStart_889970 := by decide
  rcases family_descends (prefixWord ++ tailWord_889970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_889973 : List Nat := [1, 3, 4, 3, 1, 1, 1, 7]
def baseStart_889973 : Nat := 118140960795 + 889973 * 2 ^ 59
def prefixEnd_889973 : Nat := 4983230072969 + 3 ^ 40 * 889973 * 2
def baseEnd_889973 : Nat := 67701321262807660776977

theorem tailTrace_889973 : CollatzResearch.WordTrace tailWord_889973 prefixEnd_889973 67701321262807660776977 := by
  unfold tailWord_889973
  simp only [CollatzResearch.WordTrace]
  refine ⟨32459982004787291132546573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21639988003191527421697715 32459982004787291132546573)
  ·
    refine ⟨12172493251795234174704965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32459982004787291132546573 12172493251795234174704965)
    ·
      refine ⟨2282342484711606407757181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12172493251795234174704965 2282342484711606407757181)
      ·
        refine ⟨855878431766852402908943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2282342484711606407757181 855878431766852402908943)
        ·
          refine ⟨1283817647650278604363415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 855878431766852402908943 1283817647650278604363415)
          ·
            refine ⟨1925726471475417906545123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1283817647650278604363415 1925726471475417906545123)
            ·
              refine ⟨2888589707213126859817685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1925726471475417906545123 2888589707213126859817685)
              ·
                refine ⟨67701321262807660776977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2888589707213126859817685 67701321262807660776977)
                ·
                  rfl

theorem cell21_889973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 1, 7].length) (baseStart_889973 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_889973 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_889973 prefixEnd_889973 := by exact prefixLift 889973
  have htrace : WordTrace (prefixWord ++ tailWord_889973) baseStart_889973 baseEnd_889973 := by
    simpa [prefixWord, tailWord_889973, baseEnd_889973] using wordTrace_append hprefix tailTrace_889973
  have hstable : (prefixWord ++ tailWord_889973).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_889973).length < 2 ^ (prefixWord ++ tailWord_889973).sum := by decide
  have hdescent : baseEnd_889973 < baseStart_889973 := by decide
  rcases family_descends (prefixWord ++ tailWord_889973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_889984 : List Nat := [2, 1, 1, 2, 1, 3, 3, 2, 6]
def baseStart_889984 : Nat := 118140960795 + 889984 * 2 ^ 59
def prefixEnd_889984 : Nat := 4983230072969 + 3 ^ 40 * 889984 * 2
def baseEnd_889984 : Nat := 203106474138289407647575

theorem tailTrace_889984 : CollatzResearch.WordTrace tailWord_889984 prefixEnd_889984 203106474138289407647575 := by
  unfold tailWord_889984
  simp only [CollatzResearch.WordTrace]
  refine ⟨16230191603873720005598503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21640255471831626674131337 16230191603873720005598503)
  ·
    refine ⟨24345287405810580008397755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16230191603873720005598503 24345287405810580008397755)
    ·
      refine ⟨36517931108715870012596633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24345287405810580008397755 36517931108715870012596633)
      ·
        refine ⟨27388448331536902509447475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36517931108715870012596633 27388448331536902509447475)
        ·
          refine ⟨41082672497305353764171213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27388448331536902509447475 41082672497305353764171213)
          ·
            refine ⟨15406002186489507661564205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41082672497305353764171213 15406002186489507661564205)
            ·
              refine ⟨5777250819933565373086577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15406002186489507661564205 5777250819933565373086577)
              ·
                refine ⟨4332938114950174029814933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5777250819933565373086577 4332938114950174029814933)
                ·
                  refine ⟨203106474138289407647575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4332938114950174029814933 203106474138289407647575)
                  ·
                    rfl

theorem cell21_889984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 2, 6].length) (baseStart_889984 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_889984 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_889984 prefixEnd_889984 := by exact prefixLift 889984
  have htrace : WordTrace (prefixWord ++ tailWord_889984) baseStart_889984 baseEnd_889984 := by
    simpa [prefixWord, tailWord_889984, baseEnd_889984] using wordTrace_append hprefix tailTrace_889984
  have hstable : (prefixWord ++ tailWord_889984).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_889984).length < 2 ^ (prefixWord ++ tailWord_889984).sum := by decide
  have hdescent : baseEnd_889984 < baseStart_889984 := by decide
  rcases family_descends (prefixWord ++ tailWord_889984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_890105 : List Nat := [1, 2, 1, 3, 1, 1, 3, 2, 7]
def baseStart_890105 : Nat := 118140960795 + 890105 * 2 ^ 59
def prefixEnd_890105 : Nat := 4983230072969 + 3 ^ 40 * 890105 * 2
def baseEnd_890105 : Nat := 203134087986820086130661

theorem tailTrace_890105 : CollatzResearch.WordTrace tailWord_890105 prefixEnd_890105 203134087986820086130661 := by
  unfold tailWord_890105
  simp only [CollatzResearch.WordTrace]
  refine ⟨32464796440309077676351769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21643197626872718450901179 32464796440309077676351769)
  ·
    refine ⟨24348597330231808257263827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32464796440309077676351769 24348597330231808257263827)
    ·
      refine ⟨36522895995347712385895741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24348597330231808257263827 36522895995347712385895741)
      ·
        refine ⟨13696085998255392144710903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36522895995347712385895741 13696085998255392144710903)
        ·
          refine ⟨20544128997383088217066355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13696085998255392144710903 20544128997383088217066355)
          ·
            refine ⟨30816193496074632325599533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20544128997383088217066355 30816193496074632325599533)
            ·
              refine ⟨11556072561027987122099825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30816193496074632325599533 11556072561027987122099825)
              ·
                refine ⟨8667054420770990341574869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11556072561027987122099825 8667054420770990341574869)
                ·
                  refine ⟨203134087986820086130661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8667054420770990341574869 203134087986820086130661)
                  ·
                    rfl

theorem cell21_890105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 2, 7].length) (baseStart_890105 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_890105 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_890105 prefixEnd_890105 := by exact prefixLift 890105
  have htrace : WordTrace (prefixWord ++ tailWord_890105) baseStart_890105 baseEnd_890105 := by
    simpa [prefixWord, tailWord_890105, baseEnd_890105] using wordTrace_append hprefix tailTrace_890105
  have hstable : (prefixWord ++ tailWord_890105).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_890105).length < 2 ^ (prefixWord ++ tailWord_890105).sum := by decide
  have hdescent : baseEnd_890105 < baseStart_890105 := by decide
  rcases family_descends (prefixWord ++ tailWord_890105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_890173 : List Nat := [1, 4, 1, 5, 2, 1, 1, 1, 5]
def baseStart_890173 : Nat := 118140960795 + 890173 * 2 ^ 59
def prefixEnd_890173 : Nat := 4983230072969 + 3 ^ 40 * 890173 * 2
def baseEnd_890173 : Nat := 203149606513267078997189

theorem tailTrace_890173 : CollatzResearch.WordTrace tailWord_890173 prefixEnd_890173 203149606513267078997189 := by
  unfold tailWord_890173
  simp only [CollatzResearch.WordTrace]
  refine ⟨32467276604062725289827173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21644851069375150193218115 32467276604062725289827173)
  ·
    refine ⟨6087614363261760991842595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32467276604062725289827173 6087614363261760991842595)
    ·
      refine ⟨9131421544892641487763893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6087614363261760991842595 9131421544892641487763893)
      ·
        refine ⟨856070769833685139477865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9131421544892641487763893 856070769833685139477865)
        ·
          refine ⟨642053077375263854608399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 856070769833685139477865 642053077375263854608399)
          ·
            refine ⟨963079616062895781912599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 642053077375263854608399 963079616062895781912599)
            ·
              refine ⟨1444619424094343672868899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 963079616062895781912599 1444619424094343672868899)
              ·
                refine ⟨2166929136141515509303349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1444619424094343672868899 2166929136141515509303349)
                ·
                  refine ⟨203149606513267078997189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2166929136141515509303349 203149606513267078997189)
                  ·
                    rfl

theorem cell21_890173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 1, 1, 5].length) (baseStart_890173 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_890173 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_890173 prefixEnd_890173 := by exact prefixLift 890173
  have htrace : WordTrace (prefixWord ++ tailWord_890173) baseStart_890173 baseEnd_890173 := by
    simpa [prefixWord, tailWord_890173, baseEnd_890173] using wordTrace_append hprefix tailTrace_890173
  have hstable : (prefixWord ++ tailWord_890173).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_890173).length < 2 ^ (prefixWord ++ tailWord_890173).sum := by decide
  have hdescent : baseEnd_890173 < baseStart_890173 := by decide
  rcases family_descends (prefixWord ++ tailWord_890173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_890243 : List Nat := [1, 1, 1, 3, 5, 1, 3, 6]
def baseStart_890243 : Nat := 118140960795 + 890243 * 2 ^ 59
def prefixEnd_890243 : Nat := 4983230072969 + 3 ^ 40 * 890243 * 2
def baseEnd_890243 : Nat := 67721860488987504276793

theorem tailTrace_890243 : CollatzResearch.WordTrace tailWord_890243 prefixEnd_890243 67721860488987504276793 := by
  unfold tailWord_890243
  simp only [CollatzResearch.WordTrace]
  refine ⟨32469829713809127244875383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21646553142539418163250255 32469829713809127244875383)
  ·
    refine ⟨48704744570713690867313075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32469829713809127244875383 48704744570713690867313075)
    ·
      refine ⟨73057116856070536300969613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48704744570713690867313075 73057116856070536300969613)
      ·
        refine ⟨27396418821026451112863605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73057116856070536300969613 27396418821026451112863605)
        ·
          refine ⟨2568414264471229791830963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 27396418821026451112863605 2568414264471229791830963)
          ·
            refine ⟨3852621396706844687746445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2568414264471229791830963 3852621396706844687746445)
            ·
              refine ⟨1444733023765066757904917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3852621396706844687746445 1444733023765066757904917)
              ·
                refine ⟨67721860488987504276793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1444733023765066757904917 67721860488987504276793)
                ·
                  rfl

theorem cell21_890243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 3, 6].length) (baseStart_890243 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_890243 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_890243 prefixEnd_890243 := by exact prefixLift 890243
  have htrace : WordTrace (prefixWord ++ tailWord_890243) baseStart_890243 baseEnd_890243 := by
    simpa [prefixWord, tailWord_890243, baseEnd_890243] using wordTrace_append hprefix tailTrace_890243
  have hstable : (prefixWord ++ tailWord_890243).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_890243).length < 2 ^ (prefixWord ++ tailWord_890243).sum := by decide
  have hdescent : baseEnd_890243 < baseStart_890243 := by decide
  rcases family_descends (prefixWord ++ tailWord_890243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_890257 : List Nat := [1, 2, 2, 1, 1, 1, 2, 6, 5]
def baseStart_890257 : Nat := 118140960795 + 890257 * 2 ^ 59
def prefixEnd_890257 : Nat := 4983230072969 + 3 ^ 40 * 890257 * 2
def baseEnd_890257 : Nat := 203168776457701599597017

theorem tailTrace_890257 : CollatzResearch.WordTrace tailWord_890257 prefixEnd_890257 203168776457701599597017 := by
  unfold tailWord_890257
  simp only [CollatzResearch.WordTrace]
  refine ⟨32470340335758407635885025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21646893557172271757256683 32470340335758407635885025)
  ·
    refine ⟨24352755251818805726913769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32470340335758407635885025 24352755251818805726913769)
    ·
      refine ⟨18264566438864104295185327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24352755251818805726913769 18264566438864104295185327)
      ·
        refine ⟨27396849658296156442777991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18264566438864104295185327 27396849658296156442777991)
        ·
          refine ⟨41095274487444234664166987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27396849658296156442777991 41095274487444234664166987)
          ·
            refine ⟨61642911731166351996250481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41095274487444234664166987 61642911731166351996250481)
            ·
              refine ⟨46232183798374763997187861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61642911731166351996250481 46232183798374763997187861)
              ·
                refine ⟨2167133615548817062368181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 46232183798374763997187861 2167133615548817062368181)
                ·
                  refine ⟨203168776457701599597017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2167133615548817062368181 203168776457701599597017)
                  ·
                    rfl

theorem cell21_890257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 6, 5].length) (baseStart_890257 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_890257 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_890257 prefixEnd_890257 := by exact prefixLift 890257
  have htrace : WordTrace (prefixWord ++ tailWord_890257) baseStart_890257 baseEnd_890257 := by
    simpa [prefixWord, tailWord_890257, baseEnd_890257] using wordTrace_append hprefix tailTrace_890257
  have hstable : (prefixWord ++ tailWord_890257).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_890257).length < 2 ^ (prefixWord ++ tailWord_890257).sum := by decide
  have hdescent : baseEnd_890257 < baseStart_890257 := by decide
  rcases family_descends (prefixWord ++ tailWord_890257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_890280 : List Nat := [2, 1, 6, 1, 3, 1, 1, 2, 4]
def baseStart_890280 : Nat := 118140960795 + 890280 * 2 ^ 59
def prefixEnd_890280 : Nat := 4983230072969 + 3 ^ 40 * 890280 * 2
def baseEnd_890280 : Nat := 203174025371058670713637

theorem tailTrace_890280 : CollatzResearch.WordTrace tailWord_890280 prefixEnd_890280 203174025371058670713637 := by
  unfold tailWord_890280
  simp only [CollatzResearch.WordTrace]
  refine ⟨16235589607337541281986147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21647452809783388375981529 16235589607337541281986147)
  ·
    refine ⟨24353384411006311922979221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16235589607337541281986147 24353384411006311922979221)
    ·
      refine ⟨1141564894265920871389651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 24353384411006311922979221 1141564894265920871389651)
      ·
        refine ⟨1712347341398881307084477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1141564894265920871389651 1712347341398881307084477)
        ·
          refine ⟨642130253024580490156679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1712347341398881307084477 642130253024580490156679)
          ·
            refine ⟨963195379536870735235019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 642130253024580490156679 963195379536870735235019)
            ·
              refine ⟨1444793069305306102852529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 963195379536870735235019 1444793069305306102852529)
              ·
                refine ⟨1083594801978979577139397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1444793069305306102852529 1083594801978979577139397)
                ·
                  refine ⟨203174025371058670713637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1083594801978979577139397 203174025371058670713637)
                  ·
                    rfl

theorem cell21_890280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 1, 2, 4].length) (baseStart_890280 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_890280 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_890280 prefixEnd_890280 := by exact prefixLift 890280
  have htrace : WordTrace (prefixWord ++ tailWord_890280) baseStart_890280 baseEnd_890280 := by
    simpa [prefixWord, tailWord_890280, baseEnd_890280] using wordTrace_append hprefix tailTrace_890280
  have hstable : (prefixWord ++ tailWord_890280).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_890280).length < 2 ^ (prefixWord ++ tailWord_890280).sum := by decide
  have hdescent : baseEnd_890280 < baseStart_890280 := by decide
  rcases family_descends (prefixWord ++ tailWord_890280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_890288 : List Nat := [2, 1, 1, 1, 2, 1, 1, 8, 4]
def baseStart_890288 : Nat := 118140960795 + 890288 * 2 ^ 59
def prefixEnd_890288 : Nat := 4983230072969 + 3 ^ 40 * 890288 * 2
def baseEnd_890288 : Nat := 203175851080052434580287

theorem tailTrace_890288 : CollatzResearch.WordTrace tailWord_890288 prefixEnd_890288 203175851080052434580287 := by
  unfold tailWord_890288
  simp only [CollatzResearch.WordTrace]
  refine ⟨16235735499323049965131759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21647647332430733286842345 16235735499323049965131759)
  ·
    refine ⟨24353603248984574947697639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16235735499323049965131759 24353603248984574947697639)
    ·
      refine ⟨36530404873476862421546459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24353603248984574947697639 36530404873476862421546459)
      ·
        refine ⟨54795607310215293632319689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36530404873476862421546459 54795607310215293632319689)
        ·
          refine ⟨41096705482661470224239767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54795607310215293632319689 41096705482661470224239767)
          ·
            refine ⟨61645058223992205336359651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41096705482661470224239767 61645058223992205336359651)
            ·
              refine ⟨92467587335988308004539477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61645058223992205336359651 92467587335988308004539477)
              ·
                refine ⟨1083604539093612984428197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 92467587335988308004539477 1083604539093612984428197)
                ·
                  refine ⟨203175851080052434580287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1083604539093612984428197 203175851080052434580287)
                  ·
                    rfl

theorem cell21_890288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 8, 4].length) (baseStart_890288 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_890288 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_890288 prefixEnd_890288 := by exact prefixLift 890288
  have htrace : WordTrace (prefixWord ++ tailWord_890288) baseStart_890288 baseEnd_890288 := by
    simpa [prefixWord, tailWord_890288, baseEnd_890288] using wordTrace_append hprefix tailTrace_890288
  have hstable : (prefixWord ++ tailWord_890288).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_890288).length < 2 ^ (prefixWord ++ tailWord_890288).sum := by decide
  have hdescent : baseEnd_890288 < baseStart_890288 := by decide
  rcases family_descends (prefixWord ++ tailWord_890288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_890319 : List Nat := [1, 1, 2, 1, 1, 4, 6, 5]
def baseStart_890319 : Nat := 118140960795 + 890319 * 2 ^ 59
def prefixEnd_890319 : Nat := 4983230072969 + 3 ^ 40 * 890319 * 2
def baseEnd_890319 : Nat := 67727641900801089854519

theorem tailTrace_890319 : CollatzResearch.WordTrace tailWord_890319 prefixEnd_890319 67727641900801089854519 := by
  unfold tailWord_890319
  simp only [CollatzResearch.WordTrace]
  refine ⟨32472601661533792224642011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21648401107689194816428007 32472601661533792224642011)
  ·
    refine ⟨48708902492300688336963017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32472601661533792224642011 48708902492300688336963017)
    ·
      refine ⟨36531676869225516252722263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48708902492300688336963017 36531676869225516252722263)
      ·
        refine ⟨54797515303838274379083395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36531676869225516252722263 54797515303838274379083395)
        ·
          refine ⟨82196272955757411568625093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54797515303838274379083395 82196272955757411568625093)
          ·
            refine ⟨15411801179204514669117205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82196272955757411568625093 15411801179204514669117205)
            ·
              refine ⟨722428180275211625114869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 15411801179204514669117205 722428180275211625114869)
              ·
                refine ⟨67727641900801089854519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 722428180275211625114869 67727641900801089854519)
                ·
                  rfl

theorem cell21_890319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 6, 5].length) (baseStart_890319 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_890319 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_890319 prefixEnd_890319 := by exact prefixLift 890319
  have htrace : WordTrace (prefixWord ++ tailWord_890319) baseStart_890319 baseEnd_890319 := by
    simpa [prefixWord, tailWord_890319, baseEnd_890319] using wordTrace_append hprefix tailTrace_890319
  have hstable : (prefixWord ++ tailWord_890319).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_890319).length < 2 ^ (prefixWord ++ tailWord_890319).sum := by decide
  have hdescent : baseEnd_890319 < baseStart_890319 := by decide
  rcases family_descends (prefixWord ++ tailWord_890319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_890474 : List Nat := [3, 1, 3, 2, 1, 3, 3, 1, 4]
def baseStart_890474 : Nat := 118140960795 + 890474 * 2 ^ 59
def prefixEnd_890474 : Nat := 4983230072969 + 3 ^ 40 * 890474 * 2
def baseEnd_890474 : Nat := 203218298814157444479907

theorem tailTrace_890474 : CollatzResearch.WordTrace tailWord_890474 prefixEnd_890474 203218298814157444479907 := by
  unfold tailWord_890474
  simp only [CollatzResearch.WordTrace]
  refine ⟨8119563743993063424133619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21652169983981502464356317 8119563743993063424133619)
  ·
    refine ⟨12179345615989595136200429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8119563743993063424133619 12179345615989595136200429)
    ·
      refine ⟨4567254605996098176075161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12179345615989595136200429 4567254605996098176075161)
      ·
        refine ⟨3425440954497073632056371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4567254605996098176075161 3425440954497073632056371)
        ·
          refine ⟨5138161431745610448084557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3425440954497073632056371 5138161431745610448084557)
          ·
            refine ⟨1926810536904603918031709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5138161431745610448084557 1926810536904603918031709)
            ·
              refine ⟨722553951339226469261891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1926810536904603918031709 722553951339226469261891)
              ·
                refine ⟨1083830927008839703892837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 722553951339226469261891 1083830927008839703892837)
                ·
                  refine ⟨203218298814157444479907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1083830927008839703892837 203218298814157444479907)
                  ·
                    rfl

theorem cell21_890474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 3, 1, 4].length) (baseStart_890474 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_890474 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_890474 prefixEnd_890474 := by exact prefixLift 890474
  have htrace : WordTrace (prefixWord ++ tailWord_890474) baseStart_890474 baseEnd_890474 := by
    simpa [prefixWord, tailWord_890474, baseEnd_890474] using wordTrace_append hprefix tailTrace_890474
  have hstable : (prefixWord ++ tailWord_890474).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_890474).length < 2 ^ (prefixWord ++ tailWord_890474).sum := by decide
  have hdescent : baseEnd_890474 < baseStart_890474 := by decide
  rcases family_descends (prefixWord ++ tailWord_890474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_890533 : List Nat := [1, 3, 1, 2, 1, 2, 6, 1, 4]
def baseStart_890533 : Nat := 118140960795 + 890533 * 2 ^ 59
def prefixEnd_890533 : Nat := 4983230072969 + 3 ^ 40 * 890533 * 2
def baseEnd_890533 : Nat := 203231763417986452996453

theorem tailTrace_890533 : CollatzResearch.WordTrace tailWord_890533 prefixEnd_890533 203231763417986452996453 := by
  unfold tailWord_890533
  simp only [CollatzResearch.WordTrace]
  refine ⟨32480406882758506772932253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21653604588505671181954835 32480406882758506772932253)
  ·
    refine ⟨12180152581034440039849595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32480406882758506772932253 12180152581034440039849595)
    ·
      refine ⟨18270228871551660059774393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12180152581034440039849595 18270228871551660059774393)
      ·
        refine ⟨13702671653663745044830795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18270228871551660059774393 13702671653663745044830795)
        ·
          refine ⟨20554007480495617567246193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13702671653663745044830795 20554007480495617567246193)
          ·
            refine ⟨15415505610371713175434645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20554007480495617567246193 15415505610371713175434645)
            ·
              refine ⟨722601825486174055098499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 15415505610371713175434645 722601825486174055098499)
              ·
                refine ⟨1083902738229261082647749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 722601825486174055098499 1083902738229261082647749)
                ·
                  refine ⟨203231763417986452996453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1083902738229261082647749 203231763417986452996453)
                  ·
                    rfl

theorem cell21_890533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 6, 1, 4].length) (baseStart_890533 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_890533 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_890533 prefixEnd_890533 := by exact prefixLift 890533
  have htrace : WordTrace (prefixWord ++ tailWord_890533) baseStart_890533 baseEnd_890533 := by
    simpa [prefixWord, tailWord_890533, baseEnd_890533] using wordTrace_append hprefix tailTrace_890533
  have hstable : (prefixWord ++ tailWord_890533).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_890533).length < 2 ^ (prefixWord ++ tailWord_890533).sum := by decide
  have hdescent : baseEnd_890533 < baseStart_890533 := by decide
  rcases family_descends (prefixWord ++ tailWord_890533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_890575 : List Nat := [1, 1, 2, 1, 1, 3, 1, 5, 6]
def baseStart_890575 : Nat := 118140960795 + 890575 * 2 ^ 59
def prefixEnd_890575 : Nat := 4983230072969 + 3 ^ 40 * 890575 * 2
def baseEnd_890575 : Nat := 203241348390203713296367

theorem tailTrace_890575 : CollatzResearch.WordTrace tailWord_890575 prefixEnd_890575 203241348390203713296367 := by
  unfold tailWord_890575
  simp only [CollatzResearch.WordTrace]
  refine ⟨32481938748606347945961179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21654625832404231963974119 32481938748606347945961179)
  ·
    refine ⟨48722908122909521918941769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32481938748606347945961179 48722908122909521918941769)
    ·
      refine ⟨36542181092182141439206327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48722908122909521918941769 36542181092182141439206327)
      ·
        refine ⟨54813271638273212158809491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36542181092182141439206327 54813271638273212158809491)
        ·
          refine ⟨82219907457409818238214237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54813271638273212158809491 82219907457409818238214237)
          ·
            refine ⟨30832465296528681839330339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82219907457409818238214237 30832465296528681839330339)
            ·
              refine ⟨46248697944793022758995509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30832465296528681839330339 46248697944793022758995509)
              ·
                refine ⟨4335815432324345883655829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46248697944793022758995509 4335815432324345883655829)
                ·
                  refine ⟨203241348390203713296367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4335815432324345883655829 203241348390203713296367)
                  ·
                    rfl

theorem cell21_890575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 5, 6].length) (baseStart_890575 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_890575 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_890575 prefixEnd_890575 := by exact prefixLift 890575
  have htrace : WordTrace (prefixWord ++ tailWord_890575) baseStart_890575 baseEnd_890575 := by
    simpa [prefixWord, tailWord_890575, baseEnd_890575] using wordTrace_append hprefix tailTrace_890575
  have hstable : (prefixWord ++ tailWord_890575).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_890575).length < 2 ^ (prefixWord ++ tailWord_890575).sum := by decide
  have hdescent : baseEnd_890575 < baseStart_890575 := by decide
  rcases family_descends (prefixWord ++ tailWord_890575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_890592 : List Nat := [2, 1, 1, 3, 1, 2, 4, 3, 4]
def baseStart_890592 : Nat := 118140960795 + 890592 * 2 ^ 59
def prefixEnd_890592 : Nat := 4983230072969 + 3 ^ 40 * 890592 * 2
def baseEnd_890592 : Nat := 203245228021815461512999

theorem tailTrace_890592 : CollatzResearch.WordTrace tailWord_890592 prefixEnd_890592 203245228021815461512999 := by
  unfold tailWord_890592
  simp only [CollatzResearch.WordTrace]
  refine ⟨16241279394772379924665015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21655039193029839899553353 16241279394772379924665015)
  ·
    refine ⟨24361919092158569886997523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16241279394772379924665015 24361919092158569886997523)
    ·
      refine ⟨36542878638237854830496285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24361919092158569886997523 36542878638237854830496285)
      ·
        refine ⟨13703579489339195561436107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36542878638237854830496285 13703579489339195561436107)
        ·
          refine ⟨20555369234008793342154161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13703579489339195561436107 20555369234008793342154161)
          ·
            refine ⟨15416526925506595006615621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20555369234008793342154161 15416526925506595006615621)
            ·
              refine ⟨2890598798532486563740429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15416526925506595006615621 2890598798532486563740429)
              ·
                refine ⟨1083974549449682461402661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2890598798532486563740429 1083974549449682461402661)
                ·
                  refine ⟨203245228021815461512999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1083974549449682461402661 203245228021815461512999)
                  ·
                    rfl

theorem cell21_890592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 4, 3, 4].length) (baseStart_890592 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_890592 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_890592 prefixEnd_890592 := by exact prefixLift 890592
  have htrace : WordTrace (prefixWord ++ tailWord_890592) baseStart_890592 baseEnd_890592 := by
    simpa [prefixWord, tailWord_890592, baseEnd_890592] using wordTrace_append hprefix tailTrace_890592
  have hstable : (prefixWord ++ tailWord_890592).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_890592).length < 2 ^ (prefixWord ++ tailWord_890592).sum := by decide
  have hdescent : baseEnd_890592 < baseStart_890592 := by decide
  rcases family_descends (prefixWord ++ tailWord_890592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_890682 : List Nat := [3, 1, 1, 1, 5, 1, 9]
def baseStart_890682 : Nat := 118140960795 + 890682 * 2 ^ 59
def prefixEnd_890682 : Nat := 4983230072969 + 3 ^ 40 * 890682 * 2
def baseEnd_890682 : Nat := 22585085249777256112535

theorem tailTrace_890682 : CollatzResearch.WordTrace tailWord_890682 prefixEnd_890682 22585085249777256112535 := by
  unfold tailWord_890682
  simp only [CollatzResearch.WordTrace]
  refine ⟨8121460339804676305026575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21657227572812470146737533 8121460339804676305026575)
  ·
    refine ⟨12182190509707014457539863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8121460339804676305026575 12182190509707014457539863)
    ·
      refine ⟨18273285764560521686309795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12182190509707014457539863 18273285764560521686309795)
      ·
        refine ⟨27409928646840782529464693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18273285764560521686309795 27409928646840782529464693)
        ·
          refine ⟨2569680810641323362137315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 27409928646840782529464693 2569680810641323362137315)
          ·
            refine ⟨3854521215961985043205973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2569680810641323362137315 3854521215961985043205973)
            ·
              refine ⟨22585085249777256112535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3854521215961985043205973 22585085249777256112535)
              ·
                rfl

theorem cell21_890682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 9].length) (baseStart_890682 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_890682 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_890682 prefixEnd_890682 := by exact prefixLift 890682
  have htrace : WordTrace (prefixWord ++ tailWord_890682) baseStart_890682 baseEnd_890682 := by
    simpa [prefixWord, tailWord_890682, baseEnd_890682] using wordTrace_append hprefix tailTrace_890682
  have hstable : (prefixWord ++ tailWord_890682).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_890682).length < 2 ^ (prefixWord ++ tailWord_890682).sum := by decide
  have hdescent : baseEnd_890682 < baseStart_890682 := by decide
  rcases family_descends (prefixWord ++ tailWord_890682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_890775 : List Nat := [1, 1, 3, 3, 1, 4, 3, 5]
def baseStart_890775 : Nat := 118140960795 + 890775 * 2 ^ 59
def prefixEnd_890775 : Nat := 4983230072969 + 3 ^ 40 * 890775 * 2
def baseEnd_890775 : Nat := 67762330371682603320875

theorem tailTrace_890775 : CollatzResearch.WordTrace tailWord_890775 prefixEnd_890775 67762330371682603320875 := by
  unfold tailWord_890775
  simp only [CollatzResearch.WordTrace]
  refine ⟨32489233347881782103241779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21659488898587854735494519 32489233347881782103241779)
  ·
    refine ⟨48733850021822673154862669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32489233347881782103241779 48733850021822673154862669)
    ·
      refine ⟨18275193758183502433073501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48733850021822673154862669 18275193758183502433073501)
      ·
        refine ⟨6853197659318813412402563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18275193758183502433073501 6853197659318813412402563)
        ·
          refine ⟨10279796488978220118603845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6853197659318813412402563 10279796488978220118603845)
          ·
            refine ⟨1927461841683416272238221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10279796488978220118603845 1927461841683416272238221)
            ·
              refine ⟨722798190631281102089333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1927461841683416272238221 722798190631281102089333)
              ·
                refine ⟨67762330371682603320875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 722798190631281102089333 67762330371682603320875)
                ·
                  rfl

theorem cell21_890775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 3, 5].length) (baseStart_890775 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_890775 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_890775 prefixEnd_890775 := by exact prefixLift 890775
  have htrace : WordTrace (prefixWord ++ tailWord_890775) baseStart_890775 baseEnd_890775 := by
    simpa [prefixWord, tailWord_890775, baseEnd_890775] using wordTrace_append hprefix tailTrace_890775
  have hstable : (prefixWord ++ tailWord_890775).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_890775).length < 2 ^ (prefixWord ++ tailWord_890775).sum := by decide
  have hdescent : baseEnd_890775 < baseStart_890775 := by decide
  rcases family_descends (prefixWord ++ tailWord_890775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_890792 : List Nat := [2, 1, 6, 2, 1, 1, 8]
def baseStart_890792 : Nat := 118140960795 + 890792 * 2 ^ 59
def prefixEnd_890792 : Nat := 4983230072969 + 3 ^ 40 * 890792 * 2
def baseEnd_890792 : Nat := 22587874527406617575473

theorem tailTrace_890792 : CollatzResearch.WordTrace tailWord_890792 prefixEnd_890792 22587874527406617575473 := by
  unfold tailWord_890792
  simp only [CollatzResearch.WordTrace]
  refine ⟨16244926694410097003305315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21659902259213462671073753 16244926694410097003305315)
  ·
    refine ⟨24367390041615145504957973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16244926694410097003305315 24367390041615145504957973)
    ·
      refine ⟨1142221408200709945544905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 24367390041615145504957973 1142221408200709945544905)
      ·
        refine ⟨856666056150532459158679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1142221408200709945544905 856666056150532459158679)
        ·
          refine ⟨1284999084225798688738019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 856666056150532459158679 1284999084225798688738019)
          ·
            refine ⟨1927498626338698033107029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1284999084225798688738019 1927498626338698033107029)
            ·
              refine ⟨22587874527406617575473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1927498626338698033107029 22587874527406617575473)
              ·
                rfl

theorem cell21_890792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 8].length) (baseStart_890792 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_890792 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_890792 prefixEnd_890792 := by exact prefixLift 890792
  have htrace : WordTrace (prefixWord ++ tailWord_890792) baseStart_890792 baseEnd_890792 := by
    simpa [prefixWord, tailWord_890792, baseEnd_890792] using wordTrace_append hprefix tailTrace_890792
  have hstable : (prefixWord ++ tailWord_890792).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_890792).length < 2 ^ (prefixWord ++ tailWord_890792).sum := by decide
  have hdescent : baseEnd_890792 < baseStart_890792 := by decide
  rcases family_descends (prefixWord ++ tailWord_890792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_890803 : List Nat := [1, 1, 1, 2, 3, 1, 5, 1, 6]
def baseStart_890803 : Nat := 118140960795 + 890803 * 2 ^ 59
def prefixEnd_890803 : Nat := 4983230072969 + 3 ^ 40 * 890803 * 2
def baseEnd_890803 : Nat := 203293381096525983495901

theorem tailTrace_890803 : CollatzResearch.WordTrace tailWord_890803 prefixEnd_890803 203293381096525983495901 := by
  unfold tailWord_890803
  simp only [CollatzResearch.WordTrace]
  refine ⟨32490254591780342885261063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21660169727853561923507375 32490254591780342885261063)
  ·
    refine ⟨48735381887670514327891595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32490254591780342885261063 48735381887670514327891595)
    ·
      refine ⟨73103072831505771491837393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48735381887670514327891595 73103072831505771491837393)
      ·
        refine ⟨54827304623629328618878045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73103072831505771491837393 54827304623629328618878045)
        ·
          refine ⟨20560239233860998232079267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54827304623629328618878045 20560239233860998232079267)
          ·
            refine ⟨30840358850791497348118901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20560239233860998232079267 30840358850791497348118901)
            ·
              refine ⟨2891283642261702876386147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30840358850791497348118901 2891283642261702876386147)
              ·
                refine ⟨4336925463392554314579221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2891283642261702876386147 4336925463392554314579221)
                ·
                  refine ⟨203293381096525983495901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4336925463392554314579221 203293381096525983495901)
                  ·
                    rfl

theorem cell21_890803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 5, 1, 6].length) (baseStart_890803 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_890803 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_890803 prefixEnd_890803 := by exact prefixLift 890803
  have htrace : WordTrace (prefixWord ++ tailWord_890803) baseStart_890803 baseEnd_890803 := by
    simpa [prefixWord, tailWord_890803, baseEnd_890803] using wordTrace_append hprefix tailTrace_890803
  have hstable : (prefixWord ++ tailWord_890803).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_890803).length < 2 ^ (prefixWord ++ tailWord_890803).sum := by decide
  have hdescent : baseEnd_890803 < baseStart_890803 := by decide
  rcases family_descends (prefixWord ++ tailWord_890803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_890848 : List Nat := [2, 1, 1, 3, 1, 1, 1, 4, 7]
def baseStart_890848 : Nat := 118140960795 + 890848 * 2 ^ 59
def prefixEnd_890848 : Nat := 4983230072969 + 3 ^ 40 * 890848 * 2
def baseEnd_890848 : Nat := 203303650709615905245809

theorem tailTrace_890848 : CollatzResearch.WordTrace tailWord_890848 prefixEnd_890848 203303650709615905245809 := by
  unfold tailWord_890848
  simp only [CollatzResearch.WordTrace]
  refine ⟨16245947938308657785324599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21661263917744877047099465 16245947938308657785324599)
  ·
    refine ⟨24368921907462986677986899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16245947938308657785324599 24368921907462986677986899)
    ·
      refine ⟨36553382861194480016980349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24368921907462986677986899 36553382861194480016980349)
      ·
        refine ⟨13707518572947930006367631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36553382861194480016980349 13707518572947930006367631)
        ·
          refine ⟨20561277859421895009551447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13707518572947930006367631 20561277859421895009551447)
          ·
            refine ⟨30841916789132842514327171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20561277859421895009551447 30841916789132842514327171)
            ·
              refine ⟨46262875183699263771490757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30841916789132842514327171 46262875183699263771490757)
              ·
                refine ⟨8674289096943611957154517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46262875183699263771490757 8674289096943611957154517)
                ·
                  refine ⟨203303650709615905245809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8674289096943611957154517 203303650709615905245809)
                  ·
                    rfl

theorem cell21_890848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 4, 7].length) (baseStart_890848 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_890848 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_890848 prefixEnd_890848 := by exact prefixLift 890848
  have htrace : WordTrace (prefixWord ++ tailWord_890848) baseStart_890848 baseEnd_890848 := by
    simpa [prefixWord, tailWord_890848, baseEnd_890848] using wordTrace_append hprefix tailTrace_890848
  have hstable : (prefixWord ++ tailWord_890848).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_890848).length < 2 ^ (prefixWord ++ tailWord_890848).sum := by decide
  have hdescent : baseEnd_890848 < baseStart_890848 := by decide
  rcases family_descends (prefixWord ++ tailWord_890848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_890913 : List Nat := [1, 2, 3, 2, 4, 1, 2, 2, 4]
def baseStart_890913 : Nat := 118140960795 + 890913 * 2 ^ 59
def prefixEnd_890913 : Nat := 4983230072969 + 3 ^ 40 * 890913 * 2
def baseEnd_890913 : Nat := 203318484595190236662343

theorem tailTrace_890913 : CollatzResearch.WordTrace tailWord_890913 prefixEnd_890913 203318484595190236662343 := by
  unfold tailWord_890913
  simp only [CollatzResearch.WordTrace]
  refine ⟨32494266621381831671765393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21662844414254554447843595 32494266621381831671765393)
  ·
    refine ⟨24370699966036373753824045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32494266621381831671765393 24370699966036373753824045)
    ·
      refine ⟨9139012487263640157684017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24370699966036373753824045 9139012487263640157684017)
      ·
        refine ⟨6854259365447730118263013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9139012487263640157684017 6854259365447730118263013)
        ·
          refine ⟨1285173631021449397174315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6854259365447730118263013 1285173631021449397174315)
          ·
            refine ⟨1927760446532174095761473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1285173631021449397174315 1927760446532174095761473)
            ·
              refine ⟨1445820334899130571821105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1927760446532174095761473 1445820334899130571821105)
              ·
                refine ⟨1084365251174347928865829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1445820334899130571821105 1084365251174347928865829)
                ·
                  refine ⟨203318484595190236662343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1084365251174347928865829 203318484595190236662343)
                  ·
                    rfl

theorem cell21_890913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 2, 2, 4].length) (baseStart_890913 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_890913 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_890913 prefixEnd_890913 := by exact prefixLift 890913
  have htrace : WordTrace (prefixWord ++ tailWord_890913) baseStart_890913 baseEnd_890913 := by
    simpa [prefixWord, tailWord_890913, baseEnd_890913] using wordTrace_append hprefix tailTrace_890913
  have hstable : (prefixWord ++ tailWord_890913).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_890913).length < 2 ^ (prefixWord ++ tailWord_890913).sum := by decide
  have hdescent : baseEnd_890913 < baseStart_890913 := by decide
  rcases family_descends (prefixWord ++ tailWord_890913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_890941 : List Nat := [1, 4, 1, 3, 1, 1, 3, 2, 5]
def baseStart_890941 : Nat := 118140960795 + 890941 * 2 ^ 59
def prefixEnd_890941 : Nat := 4983230072969 + 3 ^ 40 * 890941 * 2
def baseEnd_890941 : Nat := 203324874576668410195619

theorem tailTrace_890941 : CollatzResearch.WordTrace tailWord_890941 prefixEnd_890941 203324874576668410195619 := by
  unfold tailWord_890941
  simp only [CollatzResearch.WordTrace]
  refine ⟨32495287865280392453784677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21663525243520261635856451 32495287865280392453784677)
  ·
    refine ⟨6092866474740073585084627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32495287865280392453784677 6092866474740073585084627)
    ·
      refine ⟨9139299712110110377626941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6092866474740073585084627 9139299712110110377626941)
      ·
        refine ⟨3427237392041291391610103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9139299712110110377626941 3427237392041291391610103)
        ·
          refine ⟨5140856088061937087415155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3427237392041291391610103 5140856088061937087415155)
          ·
            refine ⟨7711284132092905631122733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5140856088061937087415155 7711284132092905631122733)
            ·
              refine ⟨2891731549534839611671025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7711284132092905631122733 2891731549534839611671025)
              ·
                refine ⟨2168798662151129708753269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2891731549534839611671025 2168798662151129708753269)
                ·
                  refine ⟨203324874576668410195619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2168798662151129708753269 203324874576668410195619)
                  ·
                    rfl

theorem cell21_890941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 3, 2, 5].length) (baseStart_890941 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_890941 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_890941 prefixEnd_890941 := by exact prefixLift 890941
  have htrace : WordTrace (prefixWord ++ tailWord_890941) baseStart_890941 baseEnd_890941 := by
    simpa [prefixWord, tailWord_890941, baseEnd_890941] using wordTrace_append hprefix tailTrace_890941
  have hstable : (prefixWord ++ tailWord_890941).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_890941).length < 2 ^ (prefixWord ++ tailWord_890941).sum := by decide
  have hdescent : baseEnd_890941 < baseStart_890941 := by decide
  rcases family_descends (prefixWord ++ tailWord_890941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_890958 : List Nat := [4, 1, 1, 1, 1, 4, 1, 5, 3]
def baseStart_890958 : Nat := 118140960795 + 890958 * 2 ^ 59
def prefixEnd_890958 : Nat := 4983230072969 + 3 ^ 40 * 890958 * 2
def baseEnd_890958 : Nat := 203328754208280158412251

theorem tailTrace_890958 : CollatzResearch.WordTrace tailWord_890958 prefixEnd_890958 203328754208280158412251 := by
  unfold tailWord_890958
  simp only [CollatzResearch.WordTrace]
  refine ⟨4061988488277350544644191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21663938604145869571435685 4061988488277350544644191)
  ·
    refine ⟨6092982732416025816966287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4061988488277350544644191 6092982732416025816966287)
    ·
      refine ⟨9139474098624038725449431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6092982732416025816966287 9139474098624038725449431)
      ·
        refine ⟨13709211147936058088174147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9139474098624038725449431 13709211147936058088174147)
        ·
          refine ⟨20563816721904087132261221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13709211147936058088174147 20563816721904087132261221)
          ·
            refine ⟨3855715635357016337298979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20563816721904087132261221 3855715635357016337298979)
            ·
              refine ⟨5783573453035524505948469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3855715635357016337298979 5783573453035524505948469)
              ·
                refine ⟨542210011222080422432669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5783573453035524505948469 542210011222080422432669)
                ·
                  refine ⟨203328754208280158412251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 542210011222080422432669 203328754208280158412251)
                  ·
                    rfl

theorem cell21_890958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 5, 3].length) (baseStart_890958 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_890958 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_890958 prefixEnd_890958 := by exact prefixLift 890958
  have htrace : WordTrace (prefixWord ++ tailWord_890958) baseStart_890958 baseEnd_890958 := by
    simpa [prefixWord, tailWord_890958, baseEnd_890958] using wordTrace_append hprefix tailTrace_890958
  have hstable : (prefixWord ++ tailWord_890958).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_890958).length < 2 ^ (prefixWord ++ tailWord_890958).sum := by decide
  have hdescent : baseEnd_890958 < baseStart_890958 := by decide
  rcases family_descends (prefixWord ++ tailWord_890958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_890969 : List Nat := [1, 2, 1, 2, 2, 1, 12]
def baseStart_890969 : Nat := 118140960795 + 890969 * 2 ^ 59
def prefixEnd_890969 : Nat := 4983230072969 + 3 ^ 40 * 890969 * 2
def baseEnd_890969 : Nat := 22592362728682953747655

theorem tailTrace_890969 : CollatzResearch.WordTrace tailWord_890969 prefixEnd_890969 22592362728682953747655 := by
  unfold tailWord_890969
  simp only [CollatzResearch.WordTrace]
  refine ⟨32496309109178953235803961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21664206072785968823869307 32496309109178953235803961)
  ·
    refine ⟨24372231831884214926852971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32496309109178953235803961 24372231831884214926852971)
    ·
      refine ⟨36558347747826322390279457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24372231831884214926852971 36558347747826322390279457)
      ·
        refine ⟨27418760810869741792709593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36558347747826322390279457 27418760810869741792709593)
        ·
          refine ⟨20564070608152306344532195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27418760810869741792709593 20564070608152306344532195)
          ·
            refine ⟨30846105912228459516798293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20564070608152306344532195 30846105912228459516798293)
            ·
              refine ⟨22592362728682953747655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 30846105912228459516798293 22592362728682953747655)
              ·
                rfl

theorem cell21_890969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 12].length) (baseStart_890969 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_890969 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_890969 prefixEnd_890969 := by exact prefixLift 890969
  have htrace : WordTrace (prefixWord ++ tailWord_890969) baseStart_890969 baseEnd_890969 := by
    simpa [prefixWord, tailWord_890969, baseEnd_890969] using wordTrace_append hprefix tailTrace_890969
  have hstable : (prefixWord ++ tailWord_890969).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_890969).length < 2 ^ (prefixWord ++ tailWord_890969).sum := by decide
  have hdescent : baseEnd_890969 < baseStart_890969 := by decide
  rcases family_descends (prefixWord ++ tailWord_890969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_890972 : List Nat := [2, 2, 4, 1, 1, 3, 1, 1, 6]
def baseStart_890972 : Nat := 118140960795 + 890972 * 2 ^ 59
def prefixEnd_890972 : Nat := 4983230072969 + 3 ^ 40 * 890972 * 2
def baseEnd_890972 : Nat := 203331949199019245178889

theorem tailTrace_890972 : CollatzResearch.WordTrace tailWord_890972 prefixEnd_890972 203331949199019245178889 := by
  unfold tailWord_890972
  simp only [CollatzResearch.WordTrace]
  refine ⟨16248209264084042374081585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21664279018778723165442113 16248209264084042374081585)
  ·
    refine ⟨12186156948063031780561189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16248209264084042374081585 12186156948063031780561189)
    ·
      refine ⟨2284904427761818458855223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12186156948063031780561189 2284904427761818458855223)
      ·
        refine ⟨3427356641642727688282835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2284904427761818458855223 3427356641642727688282835)
        ·
          refine ⟨5141034962464091532424253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3427356641642727688282835 5141034962464091532424253)
          ·
            refine ⟨1927888110924034324659095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5141034962464091532424253 1927888110924034324659095)
            ·
              refine ⟨2891832166386051486988643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1927888110924034324659095 2891832166386051486988643)
              ·
                refine ⟨4337748249579077230482965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2891832166386051486988643 4337748249579077230482965)
                ·
                  refine ⟨203331949199019245178889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4337748249579077230482965 203331949199019245178889)
                  ·
                    rfl

theorem cell21_890972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 1, 1, 6].length) (baseStart_890972 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_890972 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_890972 prefixEnd_890972 := by exact prefixLift 890972
  have htrace : WordTrace (prefixWord ++ tailWord_890972) baseStart_890972 baseEnd_890972 := by
    simpa [prefixWord, tailWord_890972, baseEnd_890972] using wordTrace_append hprefix tailTrace_890972
  have hstable : (prefixWord ++ tailWord_890972).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_890972).length < 2 ^ (prefixWord ++ tailWord_890972).sum := by decide
  have hdescent : baseEnd_890972 < baseStart_890972 := by decide
  rcases family_descends (prefixWord ++ tailWord_890972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_890989 : List Nat := [1, 5, 1, 1, 2, 1, 5, 1, 4]
def baseStart_890989 : Nat := 118140960795 + 890989 * 2 ^ 59
def prefixEnd_890989 : Nat := 4983230072969 + 3 ^ 40 * 890989 * 2
def baseEnd_890989 : Nat := 203335828830630993395521

theorem tailTrace_890989 : CollatzResearch.WordTrace tailWord_890989 prefixEnd_890989 203335828830630993395521 := by
  unfold tailWord_890989
  simp only [CollatzResearch.WordTrace]
  refine ⟨32497038569106496651532021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21664692379404331101021347 32497038569106496651532021)
  ·
    refine ⟨3046597365853734061081127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 32497038569106496651532021 3046597365853734061081127)
    ·
      refine ⟨4569896048780601091621691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3046597365853734061081127 4569896048780601091621691)
      ·
        refine ⟨6854844073170901637432537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4569896048780601091621691 6854844073170901637432537)
        ·
          refine ⟨5141133054878176228074403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6854844073170901637432537 5141133054878176228074403)
          ·
            refine ⟨7711699582317264342111605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5141133054878176228074403 7711699582317264342111605)
            ·
              refine ⟨722971835842243532072963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7711699582317264342111605 722971835842243532072963)
              ·
                refine ⟨1084457753763365298109445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 722971835842243532072963 1084457753763365298109445)
                ·
                  refine ⟨203335828830630993395521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1084457753763365298109445 203335828830630993395521)
                  ·
                    rfl

theorem cell21_890989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 5, 1, 4].length) (baseStart_890989 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_890989 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_890989 prefixEnd_890989 := by exact prefixLift 890989
  have htrace : WordTrace (prefixWord ++ tailWord_890989) baseStart_890989 baseEnd_890989 := by
    simpa [prefixWord, tailWord_890989, baseEnd_890989] using wordTrace_append hprefix tailTrace_890989
  have hstable : (prefixWord ++ tailWord_890989).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_890989).length < 2 ^ (prefixWord ++ tailWord_890989).sum := by decide
  have hdescent : baseEnd_890989 < baseStart_890989 := by decide
  rcases family_descends (prefixWord ++ tailWord_890989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_891121 : List Nat := [1, 2, 2, 2, 2, 1, 2, 9]
def baseStart_891121 : Nat := 118140960795 + 891121 * 2 ^ 59
def prefixEnd_891121 : Nat := 4983230072969 + 3 ^ 40 * 891121 * 2
def baseEnd_891121 : Nat := 67788651009676032398417

theorem tailTrace_891121 : CollatzResearch.WordTrace tailWord_891121 prefixEnd_891121 67788651009676032398417 := by
  unfold tailWord_891121
  simp only [CollatzResearch.WordTrace]
  refine ⟨32501853004628283195337217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21667902003085522130224811 32501853004628283195337217)
  ·
    refine ⟨24376389753471212396502913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32501853004628283195337217 24376389753471212396502913)
    ·
      refine ⟨18282292315103409297377185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24376389753471212396502913 18282292315103409297377185)
      ·
        refine ⟨13711719236327556973032889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18282292315103409297377185 13711719236327556973032889)
        ·
          refine ⟨10283789427245667729774667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13711719236327556973032889 10283789427245667729774667)
          ·
            refine ⟨15425684140868501594662001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10283789427245667729774667 15425684140868501594662001)
            ·
              refine ⟨11569263105651376195996501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15425684140868501594662001 11569263105651376195996501)
              ·
                refine ⟨67788651009676032398417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 11569263105651376195996501 67788651009676032398417)
                ·
                  rfl

theorem cell21_891121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 9].length) (baseStart_891121 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_891121 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_891121 prefixEnd_891121 := by exact prefixLift 891121
  have htrace : WordTrace (prefixWord ++ tailWord_891121) baseStart_891121 baseEnd_891121 := by
    simpa [prefixWord, tailWord_891121, baseEnd_891121] using wordTrace_append hprefix tailTrace_891121
  have hstable : (prefixWord ++ tailWord_891121).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_891121).length < 2 ^ (prefixWord ++ tailWord_891121).sum := by decide
  have hdescent : baseEnd_891121 < baseStart_891121 := by decide
  rcases family_descends (prefixWord ++ tailWord_891121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_891217 : List Nat := [1, 2, 2, 1, 4, 4, 2, 1, 4]
def baseStart_891217 : Nat := 118140960795 + 891217 * 2 ^ 59
def prefixEnd_891217 : Nat := 4983230072969 + 3 ^ 40 * 891217 * 2
def baseEnd_891217 : Nat := 203387861536953263595055

theorem tailTrace_891217 : CollatzResearch.WordTrace tailWord_891217 prefixEnd_891217 203387861536953263595055 := by
  unfold tailWord_891217
  simp only [CollatzResearch.WordTrace]
  refine ⟨32505354412280491590831905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21670236274853661060554603 32505354412280491590831905)
  ·
    refine ⟨24379015809210368693123929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32505354412280491590831905 24379015809210368693123929)
    ·
      refine ⟨18284261856907776519842947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24379015809210368693123929 18284261856907776519842947)
      ·
        refine ⟨27426392785361664779764421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18284261856907776519842947 27426392785361664779764421)
        ·
          refine ⟨5142448647255312146205829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27426392785361664779764421 5142448647255312146205829)
          ·
            refine ⟨964209121360371027413593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5142448647255312146205829 964209121360371027413593)
            ·
              refine ⟨723156841020278270560195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 964209121360371027413593 723156841020278270560195)
              ·
                refine ⟨1084735261530417405840293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 723156841020278270560195 1084735261530417405840293)
                ·
                  refine ⟨203387861536953263595055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1084735261530417405840293 203387861536953263595055)
                  ·
                    rfl

theorem cell21_891217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 2, 1, 4].length) (baseStart_891217 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_891217 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_891217 prefixEnd_891217 := by exact prefixLift 891217
  have htrace : WordTrace (prefixWord ++ tailWord_891217) baseStart_891217 baseEnd_891217 := by
    simpa [prefixWord, tailWord_891217, baseEnd_891217] using wordTrace_append hprefix tailTrace_891217
  have hstable : (prefixWord ++ tailWord_891217).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_891217).length < 2 ^ (prefixWord ++ tailWord_891217).sum := by decide
  have hdescent : baseEnd_891217 < baseStart_891217 := by decide
  rcases family_descends (prefixWord ++ tailWord_891217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_891254 : List Nat := [5, 1, 1, 4, 2, 1, 2, 2, 3]
def baseStart_891254 : Nat := 118140960795 + 891254 * 2 ^ 59
def prefixEnd_891254 : Nat := 4983230072969 + 3 ^ 40 * 891254 * 2
def baseEnd_891254 : Nat := 203396305441049421478313

theorem tailTrace_891254 : CollatzResearch.WordTrace tailWord_891254 prefixEnd_891254 203396305441049421478313 := by
  unfold tailWord_891254
  simp only [CollatzResearch.WordTrace]
  refine ⟨2031668994571652931870551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21671135942097631273285877 2031668994571652931870551)
  ·
    refine ⟨3047503491857479397805827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2031668994571652931870551 3047503491857479397805827)
    ·
      refine ⟨4571255237786219096708741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3047503491857479397805827 4571255237786219096708741)
      ·
        refine ⟨857110357084916080632889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4571255237786219096708741 857110357084916080632889)
        ·
          refine ⟨642832767813687060474667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 857110357084916080632889 642832767813687060474667)
          ·
            refine ⟨964249151720530590712001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 642832767813687060474667 964249151720530590712001)
            ·
              refine ⟨723186863790397943034001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 964249151720530590712001 723186863790397943034001)
              ·
                refine ⟨542390147842798457275501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 723186863790397943034001 542390147842798457275501)
                ·
                  refine ⟨203396305441049421478313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 542390147842798457275501 203396305441049421478313)
                  ·
                    rfl

theorem cell21_891254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 2, 2, 3].length) (baseStart_891254 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_891254 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_891254 prefixEnd_891254 := by exact prefixLift 891254
  have htrace : WordTrace (prefixWord ++ tailWord_891254) baseStart_891254 baseEnd_891254 := by
    simpa [prefixWord, tailWord_891254, baseEnd_891254] using wordTrace_append hprefix tailTrace_891254
  have hstable : (prefixWord ++ tailWord_891254).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_891254).length < 2 ^ (prefixWord ++ tailWord_891254).sum := by decide
  have hdescent : baseEnd_891254 < baseStart_891254 := by decide
  rcases family_descends (prefixWord ++ tailWord_891254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_891259 : List Nat := [1, 1, 1, 1, 1, 7, 1, 4, 4]
def baseStart_891259 : Nat := 118140960795 + 891259 * 2 ^ 59
def prefixEnd_891259 : Nat := 4983230072969 + 3 ^ 40 * 891259 * 2
def baseEnd_891259 : Nat := 203397446509170523894969

theorem tailTrace_891259 : CollatzResearch.WordTrace tailWord_891259 prefixEnd_891259 203397446509170523894969 := by
  unfold tailWord_891259
  simp only [CollatzResearch.WordTrace]
  refine ⟨32506886278128332763860831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21671257518752221842573887 32506886278128332763860831)
  ·
    refine ⟨48760329417192499145791247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32506886278128332763860831 48760329417192499145791247)
    ·
      refine ⟨73140494125788748718686871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48760329417192499145791247 73140494125788748718686871)
      ·
        refine ⟨109710741188683123078030307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73140494125788748718686871 109710741188683123078030307)
        ·
          refine ⟨164566111783024684617045461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109710741188683123078030307 164566111783024684617045461)
          ·
            refine ⟨3857018244914641045712003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 164566111783024684617045461 3857018244914641045712003)
            ·
              refine ⟨5785527367371961568568005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3857018244914641045712003 5785527367371961568568005)
              ·
                refine ⟨1084786381382242794106501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5785527367371961568568005 1084786381382242794106501)
                ·
                  refine ⟨203397446509170523894969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1084786381382242794106501 203397446509170523894969)
                  ·
                    rfl

theorem cell21_891259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 4, 4].length) (baseStart_891259 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_891259 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_891259 prefixEnd_891259 := by exact prefixLift 891259
  have htrace : WordTrace (prefixWord ++ tailWord_891259) baseStart_891259 baseEnd_891259 := by
    simpa [prefixWord, tailWord_891259, baseEnd_891259] using wordTrace_append hprefix tailTrace_891259
  have hstable : (prefixWord ++ tailWord_891259).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_891259).length < 2 ^ (prefixWord ++ tailWord_891259).sum := by decide
  have hdescent : baseEnd_891259 < baseStart_891259 := by decide
  rcases family_descends (prefixWord ++ tailWord_891259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_891321 : List Nat := [1, 2, 1, 4, 3, 2, 2, 1, 5]
def baseStart_891321 : Nat := 118140960795 + 891321 * 2 ^ 59
def prefixEnd_891321 : Nat := 4983230072969 + 3 ^ 40 * 891321 * 2
def baseEnd_891321 : Nat := 203411595753872193861509

theorem tailTrace_891321 : CollatzResearch.WordTrace tailWord_891321 prefixEnd_891321 203411595753872193861509 := by
  unfold tailWord_891321
  simp only [CollatzResearch.WordTrace]
  refine ⟨32509147603903717352617817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21672765069269144901745211 32509147603903717352617817)
  ·
    refine ⟨24381860702927788014463363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32509147603903717352617817 24381860702927788014463363)
    ·
      refine ⟨36572791054391682021695045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24381860702927788014463363 36572791054391682021695045)
      ·
        refine ⟨6857398322698440379067821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36572791054391682021695045 6857398322698440379067821)
        ·
          refine ⟨2571524371011915142150433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6857398322698440379067821 2571524371011915142150433)
          ·
            refine ⟨1928643278258936356612825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2571524371011915142150433 1928643278258936356612825)
            ·
              refine ⟨1446482458694202267459619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1928643278258936356612825 1446482458694202267459619)
              ·
                refine ⟨2169723688041303401189429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1446482458694202267459619 2169723688041303401189429)
                ·
                  refine ⟨203411595753872193861509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2169723688041303401189429 203411595753872193861509)
                  ·
                    rfl

theorem cell21_891321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 2, 1, 5].length) (baseStart_891321 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_891321 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_891321 prefixEnd_891321 := by exact prefixLift 891321
  have htrace : WordTrace (prefixWord ++ tailWord_891321) baseStart_891321 baseEnd_891321 := by
    simpa [prefixWord, tailWord_891321, baseEnd_891321] using wordTrace_append hprefix tailTrace_891321
  have hstable : (prefixWord ++ tailWord_891321).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_891321).length < 2 ^ (prefixWord ++ tailWord_891321).sum := by decide
  have hdescent : baseEnd_891321 < baseStart_891321 := by decide
  rcases family_descends (prefixWord ++ tailWord_891321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_891439 : List Nat := [1, 1, 2, 1, 2, 1, 1, 1, 11]
def baseStart_891439 : Nat := 118140960795 + 891439 * 2 ^ 59
def prefixEnd_891439 : Nat := 4983230072969 + 3 ^ 40 * 891439 * 2
def baseEnd_891439 : Nat := 203438524961530210894601

theorem tailTrace_891439 : CollatzResearch.WordTrace tailWord_891439 prefixEnd_891439 203438524961530210894601 := by
  unfold tailWord_891439
  simp only [CollatzResearch.WordTrace]
  refine ⟨32513451417476223505413371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21675634278317482336942247 32513451417476223505413371)
  ·
    refine ⟨48770177126214335258120057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32513451417476223505413371 48770177126214335258120057)
    ·
      refine ⟨36577632844660751443590043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48770177126214335258120057 36577632844660751443590043)
      ·
        refine ⟨54866449266991127165385065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36577632844660751443590043 54866449266991127165385065)
        ·
          refine ⟨41149836950243345374038799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54866449266991127165385065 41149836950243345374038799)
          ·
            refine ⟨61724755425365018061058199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41149836950243345374038799 61724755425365018061058199)
            ·
              refine ⟨92587133138047527091587299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61724755425365018061058199 92587133138047527091587299)
              ·
                refine ⟨138880699707071290637380949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92587133138047527091587299 138880699707071290637380949)
                ·
                  refine ⟨203438524961530210894601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 138880699707071290637380949 203438524961530210894601)
                  ·
                    rfl

theorem cell21_891439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 11].length) (baseStart_891439 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_891439 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_891439 prefixEnd_891439 := by exact prefixLift 891439
  have htrace : WordTrace (prefixWord ++ tailWord_891439) baseStart_891439 baseEnd_891439 := by
    simpa [prefixWord, tailWord_891439, baseEnd_891439] using wordTrace_append hprefix tailTrace_891439
  have hstable : (prefixWord ++ tailWord_891439).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_891439).length < 2 ^ (prefixWord ++ tailWord_891439).sum := by decide
  have hdescent : baseEnd_891439 < baseStart_891439 := by decide
  rcases family_descends (prefixWord ++ tailWord_891439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_891473 : List Nat := [1, 2, 2, 1, 3, 3, 1, 5, 3]
def baseStart_891473 : Nat := 118140960795 + 891473 * 2 ^ 59
def prefixEnd_891473 : Nat := 4983230072969 + 3 ^ 40 * 891473 * 2
def baseEnd_891473 : Nat := 203446284224753707327865

theorem tailTrace_891473 : CollatzResearch.WordTrace tailWord_891473 prefixEnd_891473 203446284224753707327865 := by
  unfold tailWord_891473
  simp only [CollatzResearch.WordTrace]
  refine ⟨32514691499353047312151073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21676460999568698208100715 32514691499353047312151073)
  ·
    refine ⟨24386018624514785484113305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32514691499353047312151073 24386018624514785484113305)
    ·
      refine ⟨18289513968386089113084979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24386018624514785484113305 18289513968386089113084979)
      ·
        refine ⟨27434270952579133669627469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18289513968386089113084979 27434270952579133669627469)
        ·
          refine ⟨10287851607217175126110301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27434270952579133669627469 10287851607217175126110301)
          ·
            refine ⟨3857944352706440672291363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10287851607217175126110301 3857944352706440672291363)
            ·
              refine ⟨5786916529059661008437045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3857944352706440672291363 5786916529059661008437045)
              ·
                refine ⟨542523424599343219540973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5786916529059661008437045 542523424599343219540973)
                ·
                  refine ⟨203446284224753707327865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 542523424599343219540973 203446284224753707327865)
                  ·
                    rfl

theorem cell21_891473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 5, 3].length) (baseStart_891473 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_891473 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_891473 prefixEnd_891473 := by exact prefixLift 891473
  have htrace : WordTrace (prefixWord ++ tailWord_891473) baseStart_891473 baseEnd_891473 := by
    simpa [prefixWord, tailWord_891473, baseEnd_891473] using wordTrace_append hprefix tailTrace_891473
  have hstable : (prefixWord ++ tailWord_891473).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_891473).length < 2 ^ (prefixWord ++ tailWord_891473).sum := by decide
  have hdescent : baseEnd_891473 < baseStart_891473 := by decide
  rcases family_descends (prefixWord ++ tailWord_891473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_891515 : List Nat := [1, 1, 1, 1, 1, 4, 2, 3, 7]
def baseStart_891515 : Nat := 118140960795 + 891515 * 2 ^ 59
def prefixEnd_891515 : Nat := 4983230072969 + 3 ^ 40 * 891515 * 2
def baseEnd_891515 : Nat := 203455869196970967627779

theorem tailTrace_891515 : CollatzResearch.WordTrace tailWord_891515 prefixEnd_891515 203455869196970967627779 := by
  unfold tailWord_891515
  simp only [CollatzResearch.WordTrace]
  refine ⟨32516223365200888485179999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21677482243467258990119999 32516223365200888485179999)
  ·
    refine ⟨48774335047801332727769999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32516223365200888485179999 48774335047801332727769999)
    ·
      refine ⟨73161502571701999091654999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48774335047801332727769999 73161502571701999091654999)
      ·
        refine ⟨109742253857552998637482499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73161502571701999091654999 109742253857552998637482499)
        ·
          refine ⟨164613380786329497956223749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109742253857552998637482499 164613380786329497956223749)
          ·
            refine ⟨30865008897436780866791953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 164613380786329497956223749 30865008897436780866791953)
            ·
              refine ⟨23148756673077585650093965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30865008897436780866791953 23148756673077585650093965)
              ·
                refine ⟨8680783752404094618785237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23148756673077585650093965 8680783752404094618785237)
                ·
                  refine ⟨203455869196970967627779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8680783752404094618785237 203455869196970967627779)
                  ·
                    rfl

theorem cell21_891515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 3, 7].length) (baseStart_891515 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_891515 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_891515 prefixEnd_891515 := by exact prefixLift 891515
  have htrace : WordTrace (prefixWord ++ tailWord_891515) baseStart_891515 baseEnd_891515 := by
    simpa [prefixWord, tailWord_891515, baseEnd_891515] using wordTrace_append hprefix tailTrace_891515
  have hstable : (prefixWord ++ tailWord_891515).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_891515).length < 2 ^ (prefixWord ++ tailWord_891515).sum := by decide
  have hdescent : baseEnd_891515 < baseStart_891515 := by decide
  rcases family_descends (prefixWord ++ tailWord_891515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_891549 : List Nat := [1, 4, 2, 1, 1, 1, 2, 6, 3]
def baseStart_891549 : Nat := 118140960795 + 891549 * 2 ^ 59
def prefixEnd_891549 : Nat := 4983230072969 + 3 ^ 40 * 891549 * 2
def baseEnd_891549 : Nat := 203463628460194464061043

theorem tailTrace_891549 : CollatzResearch.WordTrace tailWord_891549 prefixEnd_891549 203463628460194464061043 := by
  unfold tailWord_891549
  simp only [CollatzResearch.WordTrace]
  refine ⟨32517463447077712291917701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21678308964718474861278467 32517463447077712291917701)
  ·
    refine ⟨6097024396327071054734569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32517463447077712291917701 6097024396327071054734569)
    ·
      refine ⟨4572768297245303291050927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6097024396327071054734569 4572768297245303291050927)
      ·
        refine ⟨6859152445867954936576391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4572768297245303291050927 6859152445867954936576391)
        ·
          refine ⟨10288728668801932404864587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6859152445867954936576391 10288728668801932404864587)
          ·
            refine ⟨15433093003202898607296881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10288728668801932404864587 15433093003202898607296881)
            ·
              refine ⟨11574819752402173955472661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15433093003202898607296881 11574819752402173955472661)
              ·
                refine ⟨542569675893851904162781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 11574819752402173955472661 542569675893851904162781)
                ·
                  refine ⟨203463628460194464061043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 542569675893851904162781 203463628460194464061043)
                  ·
                    rfl

theorem cell21_891549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 6, 3].length) (baseStart_891549 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_891549 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_891549 prefixEnd_891549 := by exact prefixLift 891549
  have htrace : WordTrace (prefixWord ++ tailWord_891549) baseStart_891549 baseEnd_891549 := by
    simpa [prefixWord, tailWord_891549, baseEnd_891549] using wordTrace_append hprefix tailTrace_891549
  have hstable : (prefixWord ++ tailWord_891549).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_891549).length < 2 ^ (prefixWord ++ tailWord_891549).sum := by decide
  have hdescent : baseEnd_891549 < baseStart_891549 := by decide
  rcases family_descends (prefixWord ++ tailWord_891549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_891591 : List Nat := [1, 1, 4, 1, 1, 1, 2, 1, 9]
def baseStart_891591 : Nat := 118140960795 + 891591 * 2 ^ 59
def prefixEnd_891591 : Nat := 4983230072969 + 3 ^ 40 * 891591 * 2
def baseEnd_891591 : Nat := 203473213432411724360957

theorem tailTrace_891591 : CollatzResearch.WordTrace tailWord_891591 prefixEnd_891591 203473213432411724360957 := by
  unfold tailWord_891591
  simp only [CollatzResearch.WordTrace]
  refine ⟨32518995312925553464946627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21679330208617035643297751 32518995312925553464946627)
  ·
    refine ⟨48778492969388330197419941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32518995312925553464946627 48778492969388330197419941)
    ·
      refine ⟨9145967431760311912016239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48778492969388330197419941 9145967431760311912016239)
      ·
        refine ⟨13718951147640467868024359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9145967431760311912016239 13718951147640467868024359)
        ·
          refine ⟨20578426721460701802036539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13718951147640467868024359 20578426721460701802036539)
          ·
            refine ⟨30867640082191052703054809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20578426721460701802036539 30867640082191052703054809)
            ·
              refine ⟨23150730061643289527291107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30867640082191052703054809 23150730061643289527291107)
              ·
                refine ⟨34726095092464934290936661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23150730061643289527291107 34726095092464934290936661)
                ·
                  refine ⟨203473213432411724360957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 34726095092464934290936661 203473213432411724360957)
                  ·
                    rfl

theorem cell21_891591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 1, 9].length) (baseStart_891591 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_891591 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_891591 prefixEnd_891591 := by exact prefixLift 891591
  have htrace : WordTrace (prefixWord ++ tailWord_891591) baseStart_891591 baseEnd_891591 := by
    simpa [prefixWord, tailWord_891591, baseEnd_891591] using wordTrace_append hprefix tailTrace_891591
  have hstable : (prefixWord ++ tailWord_891591).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_891591).length < 2 ^ (prefixWord ++ tailWord_891591).sum := by decide
  have hdescent : baseEnd_891591 < baseStart_891591 := by decide
  rcases family_descends (prefixWord ++ tailWord_891591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_891656 : List Nat := [2, 1, 3, 2, 2, 4, 1, 2, 4]
def baseStart_891656 : Nat := 118140960795 + 891656 * 2 ^ 59
def prefixEnd_891656 : Nat := 4983230072969 + 3 ^ 40 * 891656 * 2
def baseEnd_891656 : Nat := 203488047317986055777491

theorem tailTrace_891656 : CollatzResearch.WordTrace tailWord_891656 prefixEnd_891656 203488047317986055777491 := by
  unfold tailWord_891656
  simp only [CollatzResearch.WordTrace]
  refine ⟨16260683028845034783031411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21680910705126713044041881 16260683028845034783031411)
  ·
    refine ⟨24391024543267552174547117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16260683028845034783031411 24391024543267552174547117)
    ·
      refine ⟨9146634203725332065455169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24391024543267552174547117 9146634203725332065455169)
      ·
        refine ⟨6859975652793999049091377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9146634203725332065455169 6859975652793999049091377)
        ·
          refine ⟨5144981739595499286818533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6859975652793999049091377 5144981739595499286818533)
          ·
            refine ⟨964684076174156116278475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5144981739595499286818533 964684076174156116278475)
            ·
              refine ⟨1447026114261234174417713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 964684076174156116278475 1447026114261234174417713)
              ·
                refine ⟨1085269585695925630813285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1447026114261234174417713 1085269585695925630813285)
                ·
                  refine ⟨203488047317986055777491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1085269585695925630813285 203488047317986055777491)
                  ·
                    rfl

theorem cell21_891656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 1, 2, 4].length) (baseStart_891656 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_891656 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_891656 prefixEnd_891656 := by exact prefixLift 891656
  have htrace : WordTrace (prefixWord ++ tailWord_891656) baseStart_891656 baseEnd_891656 := by
    simpa [prefixWord, tailWord_891656, baseEnd_891656] using wordTrace_append hprefix tailTrace_891656
  have hstable : (prefixWord ++ tailWord_891656).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_891656).length < 2 ^ (prefixWord ++ tailWord_891656).sum := by decide
  have hdescent : baseEnd_891656 < baseStart_891656 := by decide
  rcases family_descends (prefixWord ++ tailWord_891656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_891693 : List Nat := [1, 5, 3, 2, 2, 1, 1, 3, 3]
def baseStart_891693 : Nat := 118140960795 + 891693 * 2 ^ 59
def prefixEnd_891693 : Nat := 4983230072969 + 3 ^ 40 * 891693 * 2
def baseEnd_891693 : Nat := 203496491222082213660749

theorem tailTrace_891693 : CollatzResearch.WordTrace tailWord_891693 prefixEnd_891693 203496491222082213660749 := by
  unfold tailWord_891693
  simp only [CollatzResearch.WordTrace]
  refine ⟨32522715558556024885159733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21681810372370683256773155 32522715558556024885159733)
  ·
    refine ⟨3049004583614627332983725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 32522715558556024885159733 3049004583614627332983725)
    ·
      refine ⟨1143376718855485249868897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3049004583614627332983725 1143376718855485249868897)
      ·
        refine ⟨857532539141613937401673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1143376718855485249868897 857532539141613937401673)
        ·
          refine ⟨643149404356210453051255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 857532539141613937401673 643149404356210453051255)
          ·
            refine ⟨964724106534315679576883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 643149404356210453051255 964724106534315679576883)
            ·
              refine ⟨1447086159801473519365325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 964724106534315679576883 1447086159801473519365325)
              ·
                refine ⟨542657309925552569761997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1447086159801473519365325 542657309925552569761997)
                ·
                  refine ⟨203496491222082213660749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 542657309925552569761997 203496491222082213660749)
                  ·
                    rfl

theorem cell21_891693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 1, 3, 3].length) (baseStart_891693 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_891693 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_891693 prefixEnd_891693 := by exact prefixLift 891693
  have htrace : WordTrace (prefixWord ++ tailWord_891693) baseStart_891693 baseEnd_891693 := by
    simpa [prefixWord, tailWord_891693, baseEnd_891693] using wordTrace_append hprefix tailTrace_891693
  have hstable : (prefixWord ++ tailWord_891693).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_891693).length < 2 ^ (prefixWord ++ tailWord_891693).sum := by decide
  have hdescent : baseEnd_891693 < baseStart_891693 := by decide
  rcases family_descends (prefixWord ++ tailWord_891693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_891698 : List Nat := [3, 2, 1, 1, 3, 1, 1, 1, 8]
def baseStart_891698 : Nat := 118140960795 + 891698 * 2 ^ 59
def prefixEnd_891698 : Nat := 4983230072969 + 3 ^ 40 * 891698 * 2
def baseEnd_891698 : Nat := 203497632290203316077405

theorem tailTrace_891698 : CollatzResearch.WordTrace tailWord_891698 prefixEnd_891698 203497632290203316077405 := by
  unfold tailWord_891698
  simp only [CollatzResearch.WordTrace]
  refine ⟨8130724480884477684772937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21681931949025273826061165 8130724480884477684772937)
  ·
    refine ⟨6098043360663358263579703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8130724480884477684772937 6098043360663358263579703)
    ·
      refine ⟨9147065040995037395369555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6098043360663358263579703 9147065040995037395369555)
      ·
        refine ⟨13720597561492556093054333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9147065040995037395369555 13720597561492556093054333)
        ·
          refine ⟨5145224085559708534895375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13720597561492556093054333 5145224085559708534895375)
          ·
            refine ⟨7717836128339562802343063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5145224085559708534895375 7717836128339562802343063)
            ·
              refine ⟨11576754192509344203514595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7717836128339562802343063 11576754192509344203514595)
              ·
                refine ⟨17365131288764016305271893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11576754192509344203514595 17365131288764016305271893)
                ·
                  refine ⟨203497632290203316077405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 17365131288764016305271893 203497632290203316077405)
                  ·
                    rfl

theorem cell21_891698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 1, 8].length) (baseStart_891698 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_891698 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_891698 prefixEnd_891698 := by exact prefixLift 891698
  have htrace : WordTrace (prefixWord ++ tailWord_891698) baseStart_891698 baseEnd_891698 := by
    simpa [prefixWord, tailWord_891698, baseEnd_891698] using wordTrace_append hprefix tailTrace_891698
  have hstable : (prefixWord ++ tailWord_891698).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_891698).length < 2 ^ (prefixWord ++ tailWord_891698).sum := by decide
  have hdescent : baseEnd_891698 < baseStart_891698 := by decide
  rcases family_descends (prefixWord ++ tailWord_891698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_891732 : List Nat := [2, 4, 1, 1, 4, 1, 1, 3, 4]
def baseStart_891732 : Nat := 118140960795 + 891732 * 2 ^ 59
def prefixEnd_891732 : Nat := 4983230072969 + 3 ^ 40 * 891732 * 2
def baseEnd_891732 : Nat := 203505391553426812510669

theorem tailTrace_891732 : CollatzResearch.WordTrace tailWord_891732 prefixEnd_891732 203505391553426812510669 := by
  unfold tailWord_891732
  simp only [CollatzResearch.WordTrace]
  refine ⟨16262069002707367272914725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21682758670276489697219633 16262069002707367272914725)
  ·
    refine ⟨3049137938007631363671511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16262069002707367272914725 3049137938007631363671511)
    ·
      refine ⟨4573706907011447045507267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3049137938007631363671511 4573706907011447045507267)
      ·
        refine ⟨6860560360517170568260901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4573706907011447045507267 6860560360517170568260901)
        ·
          refine ⟨1286355067596969481548919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6860560360517170568260901 1286355067596969481548919)
          ·
            refine ⟨1929532601395454222323379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1286355067596969481548919 1929532601395454222323379)
            ·
              refine ⟨2894298902093181333485069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1929532601395454222323379 2894298902093181333485069)
              ·
                refine ⟨1085362088284943000056901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2894298902093181333485069 1085362088284943000056901)
                ·
                  refine ⟨203505391553426812510669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1085362088284943000056901 203505391553426812510669)
                  ·
                    rfl

theorem cell21_891732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 1, 3, 4].length) (baseStart_891732 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_891732 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_891732 prefixEnd_891732 := by exact prefixLift 891732
  have htrace : WordTrace (prefixWord ++ tailWord_891732) baseStart_891732 baseEnd_891732 := by
    simpa [prefixWord, tailWord_891732, baseEnd_891732] using wordTrace_append hprefix tailTrace_891732
  have hstable : (prefixWord ++ tailWord_891732).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_891732).length < 2 ^ (prefixWord ++ tailWord_891732).sum := by decide
  have hdescent : baseEnd_891732 < baseStart_891732 := by decide
  rcases family_descends (prefixWord ++ tailWord_891732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_891743 : List Nat := [1, 1, 2, 3, 1, 3, 2, 1, 7]
def baseStart_891743 : Nat := 118140960795 + 891743 * 2 ^ 59
def prefixEnd_891743 : Nat := 4983230072969 + 3 ^ 40 * 891743 * 2
def baseEnd_891743 : Nat := 203507901903293237827313

theorem tailTrace_891743 : CollatzResearch.WordTrace tailWord_891743 prefixEnd_891743 203507901903293237827313 := by
  unfold tailWord_891743
  simp only [CollatzResearch.WordTrace]
  refine ⟨32524539208374883424479883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21683026138916588949653255 32524539208374883424479883)
  ·
    refine ⟨48786808812562325136719825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32524539208374883424479883 48786808812562325136719825)
    ·
      refine ⟨36590106609421743852539869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48786808812562325136719825 36590106609421743852539869)
      ·
        refine ⟨13721289978533153944702451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36590106609421743852539869 13721289978533153944702451)
        ·
          refine ⟨20581934967799730917053677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13721289978533153944702451 20581934967799730917053677)
          ·
            refine ⟨7718225612924899093895129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20581934967799730917053677 7718225612924899093895129)
            ·
              refine ⟨5788669209693674320421347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7718225612924899093895129 5788669209693674320421347)
              ·
                refine ⟨8683003814540511480632021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5788669209693674320421347 8683003814540511480632021)
                ·
                  refine ⟨203507901903293237827313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8683003814540511480632021 203507901903293237827313)
                  ·
                    rfl

theorem cell21_891743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 1, 7].length) (baseStart_891743 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_891743 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_891743 prefixEnd_891743 := by exact prefixLift 891743
  have htrace : WordTrace (prefixWord ++ tailWord_891743) baseStart_891743 baseEnd_891743 := by
    simpa [prefixWord, tailWord_891743, baseEnd_891743] using wordTrace_append hprefix tailTrace_891743
  have hstable : (prefixWord ++ tailWord_891743).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_891743).length < 2 ^ (prefixWord ++ tailWord_891743).sum := by decide
  have hdescent : baseEnd_891743 < baseStart_891743 := by decide
  rcases family_descends (prefixWord ++ tailWord_891743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_891825 : List Nat := [1, 2, 2, 4, 4, 1, 1, 2, 4]
def baseStart_891825 : Nat := 118140960795 + 891825 * 2 ^ 59
def prefixEnd_891825 : Nat := 4983230072969 + 3 ^ 40 * 891825 * 2
def baseEnd_891825 : Nat := 203526615420479317460479

theorem tailTrace_891825 : CollatzResearch.WordTrace tailWord_891825 prefixEnd_891825 203526615420479317460479 := by
  unfold tailWord_891825
  simp only [CollatzResearch.WordTrace]
  refine ⟨32527529994077811428964929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21685019996051874285976619 32527529994077811428964929)
  ·
    refine ⟨24395647495558358571723697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32527529994077811428964929 24395647495558358571723697)
    ·
      refine ⟨18296735621668768928792773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24395647495558358571723697 18296735621668768928792773)
      ·
        refine ⟨3430637929062894174148645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18296735621668768928792773 3430637929062894174148645)
        ·
          refine ⟨643244611699292657652871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3430637929062894174148645 643244611699292657652871)
          ·
            refine ⟨964866917548938986479307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 643244611699292657652871 964866917548938986479307)
            ·
              refine ⟨1447300376323408479718961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 964866917548938986479307 1447300376323408479718961)
              ·
                refine ⟨1085475282242556359789221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1447300376323408479718961 1085475282242556359789221)
                ·
                  refine ⟨203526615420479317460479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1085475282242556359789221 203526615420479317460479)
                  ·
                    rfl

theorem cell21_891825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 1, 2, 4].length) (baseStart_891825 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_891825 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_891825 prefixEnd_891825 := by exact prefixLift 891825
  have htrace : WordTrace (prefixWord ++ tailWord_891825) baseStart_891825 baseEnd_891825 := by
    simpa [prefixWord, tailWord_891825, baseEnd_891825] using wordTrace_append hprefix tailTrace_891825
  have hstable : (prefixWord ++ tailWord_891825).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_891825).length < 2 ^ (prefixWord ++ tailWord_891825).sum := by decide
  have hdescent : baseEnd_891825 < baseStart_891825 := by decide
  rcases family_descends (prefixWord ++ tailWord_891825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_891946 : List Nat := [3, 1, 4, 1, 3, 1, 1, 4, 3]
def baseStart_891946 : Nat := 118140960795 + 891946 * 2 ^ 59
def prefixEnd_891946 : Nat := 4983230072969 + 3 ^ 40 * 891946 * 2
def baseEnd_891946 : Nat := 203554229269009995943565

theorem tailTrace_891946 : CollatzResearch.WordTrace tailWord_891946 prefixEnd_891946 203554229269009995943565 := by
  unfold tailWord_891946
  simp only [CollatzResearch.WordTrace]
  refine ⟨8132985806659862273529923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21687962151092966062746461 8132985806659862273529923)
  ·
    refine ⟨12199478709989793410294885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8132985806659862273529923 12199478709989793410294885)
    ·
      refine ⟨2287402258123086264430291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12199478709989793410294885 2287402258123086264430291)
      ·
        refine ⟨3431103387184629396645437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2287402258123086264430291 3431103387184629396645437)
        ·
          refine ⟨1286663770194236023742039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3431103387184629396645437 1286663770194236023742039)
          ·
            refine ⟨1929995655291354035613059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1286663770194236023742039 1929995655291354035613059)
            ·
              refine ⟨2894993482937031053419589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1929995655291354035613059 2894993482937031053419589)
              ·
                refine ⟨542811278050693322516173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2894993482937031053419589 542811278050693322516173)
                ·
                  refine ⟨203554229269009995943565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 542811278050693322516173 203554229269009995943565)
                  ·
                    rfl

theorem cell21_891946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 1, 4, 3].length) (baseStart_891946 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_891946 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_891946 prefixEnd_891946 := by exact prefixLift 891946
  have htrace : WordTrace (prefixWord ++ tailWord_891946) baseStart_891946 baseEnd_891946 := by
    simpa [prefixWord, tailWord_891946, baseEnd_891946] using wordTrace_append hprefix tailTrace_891946
  have hstable : (prefixWord ++ tailWord_891946).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_891946).length < 2 ^ (prefixWord ++ tailWord_891946).sum := by decide
  have hdescent : baseEnd_891946 < baseStart_891946 := by decide
  rcases family_descends (prefixWord ++ tailWord_891946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_891971 : List Nat := [1, 1, 1, 3, 1, 2, 5, 2, 5]
def baseStart_891971 : Nat := 118140960795 + 891971 * 2 ^ 59
def prefixEnd_891971 : Nat := 4983230072969 + 3 ^ 40 * 891971 * 2
def baseEnd_891971 : Nat := 203559934609615508026847

theorem tailTrace_891971 : CollatzResearch.WordTrace tailWord_891971 prefixEnd_891971 203559934609615508026847 := by
  unfold tailWord_891971
  simp only [CollatzResearch.WordTrace]
  refine ⟨32532855051548878363779767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21688570034365918909186511 32532855051548878363779767)
  ·
    refine ⟨48799282577323317545669651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32532855051548878363779767 48799282577323317545669651)
    ·
      refine ⟨73198923865984976318504477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48799282577323317545669651 73198923865984976318504477)
      ·
        refine ⟨27449596449744366119439179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73198923865984976318504477 27449596449744366119439179)
        ·
          refine ⟨41174394674616549179158769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27449596449744366119439179 41174394674616549179158769)
          ·
            refine ⟨30880796005962411884369077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41174394674616549179158769 30880796005962411884369077)
            ·
              refine ⟨2895074625558976114159601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30880796005962411884369077 2895074625558976114159601)
              ·
                refine ⟨2171305969169232085619701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2895074625558976114159601 2171305969169232085619701)
                ·
                  refine ⟨203559934609615508026847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2171305969169232085619701 203559934609615508026847)
                  ·
                    rfl

theorem cell21_891971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 5, 2, 5].length) (baseStart_891971 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_891971 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_891971 prefixEnd_891971 := by exact prefixLift 891971
  have htrace : WordTrace (prefixWord ++ tailWord_891971) baseStart_891971 baseEnd_891971 := by
    simpa [prefixWord, tailWord_891971, baseEnd_891971] using wordTrace_append hprefix tailTrace_891971
  have hstable : (prefixWord ++ tailWord_891971).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_891971).length < 2 ^ (prefixWord ++ tailWord_891971).sum := by decide
  have hdescent : baseEnd_891971 < baseStart_891971 := by decide
  rcases family_descends (prefixWord ++ tailWord_891971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_892016 : List Nat := [2, 1, 1, 1, 5, 1, 2, 8]
def baseStart_892016 : Nat := 118140960795 + 892016 * 2 ^ 59
def prefixEnd_892016 : Nat := 4983230072969 + 3 ^ 40 * 892016 * 2
def baseEnd_892016 : Nat := 67856734740901809925585

theorem tailTrace_892016 : CollatzResearch.WordTrace tailWord_892016 prefixEnd_892016 67856734740901809925585 := by
  unfold tailWord_892016
  simp only [CollatzResearch.WordTrace]
  refine ⟨16267248168192925524583951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21689664224257234032778601 16267248168192925524583951)
  ·
    refine ⟨24400872252289388286875927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16267248168192925524583951 24400872252289388286875927)
    ·
      refine ⟨36601308378434082430313891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24400872252289388286875927 36601308378434082430313891)
      ·
        refine ⟨54901962567651123645470837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36601308378434082430313891 54901962567651123645470837)
        ·
          refine ⟨5147058990717292841762891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 54901962567651123645470837 5147058990717292841762891)
          ·
            refine ⟨7720588486075939262644337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5147058990717292841762891 7720588486075939262644337)
            ·
              refine ⟨5790441364556954446983253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7720588486075939262644337 5790441364556954446983253)
              ·
                refine ⟨67856734740901809925585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5790441364556954446983253 67856734740901809925585)
                ·
                  rfl

theorem cell21_892016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 8].length) (baseStart_892016 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_892016 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_892016 prefixEnd_892016 := by exact prefixLift 892016
  have htrace : WordTrace (prefixWord ++ tailWord_892016) baseStart_892016 baseEnd_892016 := by
    simpa [prefixWord, tailWord_892016, baseEnd_892016] using wordTrace_append hprefix tailTrace_892016
  have hstable : (prefixWord ++ tailWord_892016).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_892016).length < 2 ^ (prefixWord ++ tailWord_892016).sum := by decide
  have hdescent : baseEnd_892016 < baseStart_892016 := by decide
  rcases family_descends (prefixWord ++ tailWord_892016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_892033 : List Nat := [1, 2, 4, 2, 2, 2, 1, 7]
def baseStart_892033 : Nat := 118140960795 + 892033 * 2 ^ 59
def prefixEnd_892033 : Nat := 4983230072969 + 3 ^ 40 * 892033 * 2
def baseEnd_892033 : Nat := 67858027951439059331129

theorem tailTrace_892033 : CollatzResearch.WordTrace tailWord_892033 prefixEnd_892033 67858027951439059331129 := by
  unfold tailWord_892033
  simp only [CollatzResearch.WordTrace]
  refine ⟨32535116377324262952536753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21690077584882841968357835 32535116377324262952536753)
  ·
    refine ⟨24401337282993197214402565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32535116377324262952536753 24401337282993197214402565)
    ·
      refine ⟨4575250740561224477700481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24401337282993197214402565 4575250740561224477700481)
      ·
        refine ⟨3431438055420918358275361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4575250740561224477700481 3431438055420918358275361)
        ·
          refine ⟨2573578541565688768706521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3431438055420918358275361 2573578541565688768706521)
          ·
            refine ⟨1930183906174266576529891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2573578541565688768706521 1930183906174266576529891)
            ·
              refine ⟨2895275859261399864794837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1930183906174266576529891 2895275859261399864794837)
              ·
                refine ⟨67858027951439059331129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2895275859261399864794837 67858027951439059331129)
                ·
                  rfl

theorem cell21_892033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 1, 7].length) (baseStart_892033 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_892033 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_892033 prefixEnd_892033 := by exact prefixLift 892033
  have htrace : WordTrace (prefixWord ++ tailWord_892033) baseStart_892033 baseEnd_892033 := by
    simpa [prefixWord, tailWord_892033, baseEnd_892033] using wordTrace_append hprefix tailTrace_892033
  have hstable : (prefixWord ++ tailWord_892033).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_892033).length < 2 ^ (prefixWord ++ tailWord_892033).sum := by decide
  have hdescent : baseEnd_892033 < baseStart_892033 := by decide
  rcases family_descends (prefixWord ++ tailWord_892033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_892171 : List Nat := [1, 1, 1, 1, 5, 5, 1, 2, 4]
def baseStart_892171 : Nat := 118140960795 + 892171 * 2 ^ 59
def prefixEnd_892171 : Nat := 4983230072969 + 3 ^ 40 * 892171 * 2
def baseEnd_892171 : Nat := 203605577334459604693105

theorem tailTrace_892171 : CollatzResearch.WordTrace tailWord_892171 prefixEnd_892171 203605577334459604693105 := by
  unfold tailWord_892171
  simp only [CollatzResearch.WordTrace]
  refine ⟨32540149650824312521060367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21693433100549541680706911 32540149650824312521060367)
  ·
    refine ⟨48810224476236468781590551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32540149650824312521060367 48810224476236468781590551)
    ·
      refine ⟨73215336714354703172385827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48810224476236468781590551 73215336714354703172385827)
      ·
        refine ⟨109823005071532054758578741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73215336714354703172385827 109823005071532054758578741)
        ·
          refine ⟨10295906725456130133616757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 109823005071532054758578741 10295906725456130133616757)
          ·
            refine ⟨965241255511512200026571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10295906725456130133616757 965241255511512200026571)
            ·
              refine ⟨1447861883267268300039857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 965241255511512200026571 1447861883267268300039857)
              ·
                refine ⟨1085896412450451225029893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1447861883267268300039857 1085896412450451225029893)
                ·
                  refine ⟨203605577334459604693105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1085896412450451225029893 203605577334459604693105)
                  ·
                    rfl

theorem cell21_892171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 1, 2, 4].length) (baseStart_892171 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_892171 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_892171 prefixEnd_892171 := by exact prefixLift 892171
  have htrace : WordTrace (prefixWord ++ tailWord_892171) baseStart_892171 baseEnd_892171 := by
    simpa [prefixWord, tailWord_892171, baseEnd_892171] using wordTrace_append hprefix tailTrace_892171
  have hstable : (prefixWord ++ tailWord_892171).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_892171).length < 2 ^ (prefixWord ++ tailWord_892171).sum := by decide
  have hdescent : baseEnd_892171 < baseStart_892171 := by decide
  rcases family_descends (prefixWord ++ tailWord_892171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_892202 : List Nat := [3, 1, 4, 2, 1, 1, 4, 5]
def baseStart_892202 : Nat := 118140960795 + 892202 * 2 ^ 59
def prefixEnd_892202 : Nat := 4983230072969 + 3 ^ 40 * 892202 * 2
def baseEnd_892202 : Nat := 67870883985603479892125

theorem tailTrace_892202 : CollatzResearch.WordTrace tailWord_892202 prefixEnd_892202 67870883985603479892125 := by
  unfold tailWord_892202
  simp only [CollatzResearch.WordTrace]
  refine ⟨8135320078428001203859715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21694186875808003210292573 8135320078428001203859715)
  ·
    refine ⟨12202980117642001805789573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8135320078428001203859715 12202980117642001805789573)
    ·
      refine ⟨2288058772057875338585545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12202980117642001805789573 2288058772057875338585545)
      ·
        refine ⟨1716044079043406503939159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2288058772057875338585545 1716044079043406503939159)
        ·
          refine ⟨2574066118565109755908739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1716044079043406503939159 2574066118565109755908739)
          ·
            refine ⟨3861099177847664633863109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2574066118565109755908739 3861099177847664633863109)
            ·
              refine ⟨723956095846437118849333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3861099177847664633863109 723956095846437118849333)
              ·
                refine ⟨67870883985603479892125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 723956095846437118849333 67870883985603479892125)
                ·
                  rfl

theorem cell21_892202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 4, 5].length) (baseStart_892202 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_892202 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_892202 prefixEnd_892202 := by exact prefixLift 892202
  have htrace : WordTrace (prefixWord ++ tailWord_892202) baseStart_892202 baseEnd_892202 := by
    simpa [prefixWord, tailWord_892202, baseEnd_892202] using wordTrace_append hprefix tailTrace_892202
  have hstable : (prefixWord ++ tailWord_892202).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_892202).length < 2 ^ (prefixWord ++ tailWord_892202).sum := by decide
  have hdescent : baseEnd_892202 < baseStart_892202 := by decide
  rcases family_descends (prefixWord ++ tailWord_892202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_892247 : List Nat := [1, 1, 3, 2, 3, 2, 4, 1, 4]
def baseStart_892247 : Nat := 118140960795 + 892247 * 2 ^ 59
def prefixEnd_892247 : Nat := 4983230072969 + 3 ^ 40 * 892247 * 2
def baseEnd_892247 : Nat := 203622921569900361426283

theorem tailTrace_892247 : CollatzResearch.WordTrace tailWord_892247 prefixEnd_892247 203622921569900361426283 := by
  unfold tailWord_892247
  simp only [CollatzResearch.WordTrace]
  refine ⟨32542921598548977500826995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21695281065699318333884663 32542921598548977500826995)
  ·
    refine ⟨48814382397823466251240493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32542921598548977500826995 48814382397823466251240493)
    ·
      refine ⟨18305393399183799844215185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48814382397823466251240493 18305393399183799844215185)
      ·
        refine ⟨13729045049387849883161389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18305393399183799844215185 13729045049387849883161389)
        ·
          refine ⟨5148391893520443706185521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13729045049387849883161389 5148391893520443706185521)
          ·
            refine ⟨3861293920140332779639141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5148391893520443706185521 3861293920140332779639141)
            ·
              refine ⟨723992610026312396182339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3861293920140332779639141 723992610026312396182339)
              ·
                refine ⟨1085988915039468594273509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 723992610026312396182339 1085988915039468594273509)
                ·
                  refine ⟨203622921569900361426283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1085988915039468594273509 203622921569900361426283)
                  ·
                    rfl

theorem cell21_892247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 4, 1, 4].length) (baseStart_892247 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_892247 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_892247 prefixEnd_892247 := by exact prefixLift 892247
  have htrace : WordTrace (prefixWord ++ tailWord_892247) baseStart_892247 baseEnd_892247 := by
    simpa [prefixWord, tailWord_892247, baseEnd_892247] using wordTrace_append hprefix tailTrace_892247
  have hstable : (prefixWord ++ tailWord_892247).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_892247).length < 2 ^ (prefixWord ++ tailWord_892247).sum := by decide
  have hdescent : baseEnd_892247 < baseStart_892247 := by decide
  rcases family_descends (prefixWord ++ tailWord_892247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_892385 : List Nat := [1, 2, 3, 1, 2, 5, 1, 3, 3]
def baseStart_892385 : Nat := 118140960795 + 892385 * 2 ^ 59
def prefixEnd_892385 : Nat := 4983230072969 + 3 ^ 40 * 892385 * 2
def baseEnd_892385 : Nat := 203654415050042788126001

theorem tailTrace_892385 : CollatzResearch.WordTrace tailWord_892385 prefixEnd_892385 203654415050042788126001 := by
  unfold tailWord_892385
  simp only [CollatzResearch.WordTrace]
  refine ⟨32547954872049027069350609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21698636581366018046233739 32547954872049027069350609)
  ·
    refine ⟨24410966154036770302012957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32547954872049027069350609 24410966154036770302012957)
    ·
      refine ⟨9154112307763788863254859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24410966154036770302012957 9154112307763788863254859)
      ·
        refine ⟨13731168461645683294882289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9154112307763788863254859 13731168461645683294882289)
        ·
          refine ⟨10298376346234262471161717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13731168461645683294882289 10298376346234262471161717)
          ·
            refine ⟨965472782459462106671411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10298376346234262471161717 965472782459462106671411)
            ·
              refine ⟨1448209173689193160007117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 965472782459462106671411 1448209173689193160007117)
              ·
                refine ⟨543078440133447435002669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1448209173689193160007117 543078440133447435002669)
                ·
                  refine ⟨203654415050042788126001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 543078440133447435002669 203654415050042788126001)
                  ·
                    rfl

theorem cell21_892385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 1, 3, 3].length) (baseStart_892385 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_892385 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_892385 prefixEnd_892385 := by exact prefixLift 892385
  have htrace : WordTrace (prefixWord ++ tailWord_892385) baseStart_892385 baseEnd_892385 := by
    simpa [prefixWord, tailWord_892385, baseEnd_892385] using wordTrace_append hprefix tailTrace_892385
  have hstable : (prefixWord ++ tailWord_892385).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_892385).length < 2 ^ (prefixWord ++ tailWord_892385).sum := by decide
  have hdescent : baseEnd_892385 < baseStart_892385 := by decide
  rcases family_descends (prefixWord ++ tailWord_892385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_892402 : List Nat := [3, 2, 1, 4, 1, 2, 3, 2, 3]
def baseStart_892402 : Nat := 118140960795 + 892402 * 2 ^ 59
def prefixEnd_892402 : Nat := 4983230072969 + 3 ^ 40 * 892402 * 2
def baseEnd_892402 : Nat := 203658294681654536342633

theorem tailTrace_892402 : CollatzResearch.WordTrace tailWord_892402 prefixEnd_892402 203658294681654536342633 := by
  unfold tailWord_892402
  simp only [CollatzResearch.WordTrace]
  refine ⟨8137143728246859743179865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21699049941991625981812973 8137143728246859743179865)
  ·
    refine ⟨6102857796185144807384899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8137143728246859743179865 6102857796185144807384899)
    ·
      refine ⟨9154286694277717211077349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6102857796185144807384899 9154286694277717211077349)
      ·
        refine ⟨1716428755177071977077003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9154286694277717211077349 1716428755177071977077003)
        ·
          refine ⟨2574643132765607965615505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1716428755177071977077003 2574643132765607965615505)
          ·
            refine ⟨1930982349574205974211629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2574643132765607965615505 1930982349574205974211629)
            ·
              refine ⟨724118381090327240329361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1930982349574205974211629 724118381090327240329361)
              ·
                refine ⟨543088785817745430247021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 724118381090327240329361 543088785817745430247021)
                ·
                  refine ⟨203658294681654536342633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 543088785817745430247021 203658294681654536342633)
                  ·
                    rfl

theorem cell21_892402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 3, 2, 3].length) (baseStart_892402 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_892402 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_892402 prefixEnd_892402 := by exact prefixLift 892402
  have htrace : WordTrace (prefixWord ++ tailWord_892402) baseStart_892402 baseEnd_892402 := by
    simpa [prefixWord, tailWord_892402, baseEnd_892402] using wordTrace_append hprefix tailTrace_892402
  have hstable : (prefixWord ++ tailWord_892402).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_892402).length < 2 ^ (prefixWord ++ tailWord_892402).sum := by decide
  have hdescent : baseEnd_892402 < baseStart_892402 := by decide
  rcases family_descends (prefixWord ++ tailWord_892402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_892444 : List Nat := [2, 2, 3, 1, 2, 1, 2, 5, 3]
def baseStart_892444 : Nat := 118140960795 + 892444 * 2 ^ 59
def prefixEnd_892444 : Nat := 4983230072969 + 3 ^ 40 * 892444 * 2
def baseEnd_892444 : Nat := 203667879653871796642547

theorem tailTrace_892444 : CollatzResearch.WordTrace tailWord_892444 prefixEnd_892444 203667879653871796642547 := by
  unfold tailWord_892444
  simp only [CollatzResearch.WordTrace]
  refine ⟨16275053389417640072874193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21700071185890186763832257 16275053389417640072874193)
  ·
    refine ⟨12206290042063230054655645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16275053389417640072874193 12206290042063230054655645)
    ·
      refine ⟨4577358765773711270495867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12206290042063230054655645 4577358765773711270495867)
      ·
        refine ⟨6866038148660566905743801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4577358765773711270495867 6866038148660566905743801)
        ·
          refine ⟨5149528611495425179307851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6866038148660566905743801 5149528611495425179307851)
          ·
            refine ⟨7724292917243137768961777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5149528611495425179307851 7724292917243137768961777)
            ·
              refine ⟨5793219687932353326721333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7724292917243137768961777 5793219687932353326721333)
              ·
                refine ⟨543114345743658124380125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5793219687932353326721333 543114345743658124380125)
                ·
                  refine ⟨203667879653871796642547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 543114345743658124380125 203667879653871796642547)
                  ·
                    rfl

theorem cell21_892444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 5, 3].length) (baseStart_892444 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_892444 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_892444 prefixEnd_892444 := by exact prefixLift 892444
  have htrace : WordTrace (prefixWord ++ tailWord_892444) baseStart_892444 baseEnd_892444 := by
    simpa [prefixWord, tailWord_892444, baseEnd_892444] using wordTrace_append hprefix tailTrace_892444
  have hstable : (prefixWord ++ tailWord_892444).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_892444).length < 2 ^ (prefixWord ++ tailWord_892444).sum := by decide
  have hdescent : baseEnd_892444 < baseStart_892444 := by decide
  rcases family_descends (prefixWord ++ tailWord_892444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_892472 : List Nat := [2, 1, 2, 1, 4, 2, 3, 6]
def baseStart_892472 : Nat := 118140960795 + 892472 * 2 ^ 59
def prefixEnd_892472 : Nat := 4983230072969 + 3 ^ 40 * 892472 * 2
def baseEnd_892472 : Nat := 67891423211783323391941

theorem tailTrace_892472 : CollatzResearch.WordTrace tailWord_892472 prefixEnd_892472 67891423211783323391941 := by
  unfold tailWord_892472
  simp only [CollatzResearch.WordTrace]
  refine ⟨16275564011366920463883835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21700752015155893951845113 16275564011366920463883835)
  ·
    refine ⟨24413346017050380695825753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16275564011366920463883835 24413346017050380695825753)
    ·
      refine ⟨18310009512787785521869315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24413346017050380695825753 18310009512787785521869315)
      ·
        refine ⟨27465014269181678282803973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18310009512787785521869315 27465014269181678282803973)
        ·
          refine ⟨5149690175471564678025745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27465014269181678282803973 5149690175471564678025745)
          ·
            refine ⟨3862267631603673508519309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5149690175471564678025745 3862267631603673508519309)
            ·
              refine ⟨1448350361851377565694741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3862267631603673508519309 1448350361851377565694741)
              ·
                refine ⟨67891423211783323391941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1448350361851377565694741 67891423211783323391941)
                ·
                  rfl

theorem cell21_892472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 3, 6].length) (baseStart_892472 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_892472 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_892472 prefixEnd_892472 := by exact prefixLift 892472
  have htrace : WordTrace (prefixWord ++ tailWord_892472) baseStart_892472 baseEnd_892472 := by
    simpa [prefixWord, tailWord_892472, baseEnd_892472] using wordTrace_append hprefix tailTrace_892472
  have hstable : (prefixWord ++ tailWord_892472).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_892472).length < 2 ^ (prefixWord ++ tailWord_892472).sum := by decide
  have hdescent : baseEnd_892472 < baseStart_892472 := by decide
  rcases family_descends (prefixWord ++ tailWord_892472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_892509 : List Nat := [1, 4, 4, 2, 1, 2, 1, 2, 4]
def baseStart_892509 : Nat := 118140960795 + 892509 * 2 ^ 59
def prefixEnd_892509 : Nat := 4983230072969 + 3 ^ 40 * 892509 * 2
def baseEnd_892509 : Nat := 203682713539446128059081

theorem tailTrace_892509 : CollatzResearch.WordTrace tailWord_892509 prefixEnd_892509 203682713539446128059081 := by
  unfold tailWord_892509
  simp only [CollatzResearch.WordTrace]
  refine ⟨32552477523599796246864581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21701651682399864164576387 32552477523599796246864581)
  ·
    refine ⟨6103589535674961796287109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32552477523599796246864581 6103589535674961796287109)
    ·
      refine ⟨1144423037939055336803833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6103589535674961796287109 1144423037939055336803833)
      ·
        refine ⟨858317278454291502602875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1144423037939055336803833 858317278454291502602875)
        ·
          refine ⟨1287475917681437253904313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 858317278454291502602875 1287475917681437253904313)
          ·
            refine ⟨965606938261077940428235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1287475917681437253904313 965606938261077940428235)
            ·
              refine ⟨1448410407391616910642353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 965606938261077940428235 1448410407391616910642353)
              ·
                refine ⟨1086307805543712682981765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1448410407391616910642353 1086307805543712682981765)
                ·
                  refine ⟨203682713539446128059081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1086307805543712682981765 203682713539446128059081)
                  ·
                    rfl

theorem cell21_892509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 1, 2, 4].length) (baseStart_892509 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_892509 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_892509 prefixEnd_892509 := by exact prefixLift 892509
  have htrace : WordTrace (prefixWord ++ tailWord_892509) baseStart_892509 baseEnd_892509 := by
    simpa [prefixWord, tailWord_892509, baseEnd_892509] using wordTrace_append hprefix tailTrace_892509
  have hstable : (prefixWord ++ tailWord_892509).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_892509).length < 2 ^ (prefixWord ++ tailWord_892509).sum := by decide
  have hdescent : baseEnd_892509 < baseStart_892509 := by decide
  rcases family_descends (prefixWord ++ tailWord_892509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_892520 : List Nat := [2, 1, 4, 3, 1, 2, 2, 1, 5]
def baseStart_892520 : Nat := 118140960795 + 892520 * 2 ^ 59
def prefixEnd_892520 : Nat := 4983230072969 + 3 ^ 40 * 892520 * 2
def baseEnd_892520 : Nat := 203685223889312553375725

theorem tailTrace_892520 : CollatzResearch.WordTrace tailWord_892520 prefixEnd_892520 203685223889312553375725 := by
  unfold tailWord_892520
  simp only [CollatzResearch.WordTrace]
  refine ⟨16276439363279972562757507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21701919151039963417010009 16276439363279972562757507)
  ·
    refine ⟨24414659044919958844136261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16276439363279972562757507 24414659044919958844136261)
    ·
      refine ⟨4577748570922492283275549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24414659044919958844136261 4577748570922492283275549)
      ·
        refine ⟨1716655714095934606228331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4577748570922492283275549 1716655714095934606228331)
        ·
          refine ⟨2574983571143901909342497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1716655714095934606228331 2574983571143901909342497)
          ·
            refine ⟨1931237678357926432006873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2574983571143901909342497 1931237678357926432006873)
            ·
              refine ⟨1448428258768444824005155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1931237678357926432006873 1448428258768444824005155)
              ·
                refine ⟨2172642388152667236007733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1448428258768444824005155 2172642388152667236007733)
                ·
                  refine ⟨203685223889312553375725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2172642388152667236007733 203685223889312553375725)
                  ·
                    rfl

theorem cell21_892520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 2, 1, 5].length) (baseStart_892520 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_892520 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_892520 prefixEnd_892520 := by exact prefixLift 892520
  have htrace : WordTrace (prefixWord ++ tailWord_892520) baseStart_892520 baseEnd_892520 := by
    simpa [prefixWord, tailWord_892520, baseEnd_892520] using wordTrace_append hprefix tailTrace_892520
  have hstable : (prefixWord ++ tailWord_892520).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_892520).length < 2 ^ (prefixWord ++ tailWord_892520).sum := by decide
  have hdescent : baseEnd_892520 < baseStart_892520 := by decide
  rcases family_descends (prefixWord ++ tailWord_892520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_892607 : List Nat := [1, 1, 2, 2, 2, 3, 1, 9]
def baseStart_892607 : Nat := 118140960795 + 892607 * 2 ^ 59
def prefixEnd_892607 : Nat := 4983230072969 + 3 ^ 40 * 892607 * 2
def baseEnd_892607 : Nat := 67901692824873245141849

theorem tailTrace_892607 : CollatzResearch.WordTrace tailWord_892607 prefixEnd_892607 67901692824873245141849 := by
  unfold tailWord_892607
  simp only [CollatzResearch.WordTrace]
  refine ⟨32556051877244758983932075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21704034584829839322621383 32556051877244758983932075)
  ·
    refine ⟨48834077815867138475898113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32556051877244758983932075 48834077815867138475898113)
    ·
      refine ⟨36625558361900353856923585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48834077815867138475898113 36625558361900353856923585)
      ·
        refine ⟨27469168771425265392692689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36625558361900353856923585 27469168771425265392692689)
        ·
          refine ⟨20601876578568949044519517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27469168771425265392692689 20601876578568949044519517)
          ·
            refine ⟨7725703716963355891694819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20601876578568949044519517 7725703716963355891694819)
            ·
              refine ⟨11588555575445033837542229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7725703716963355891694819 11588555575445033837542229)
              ·
                refine ⟨67901692824873245141849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 11588555575445033837542229 67901692824873245141849)
                ·
                  rfl

theorem cell21_892607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 9].length) (baseStart_892607 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_892607 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_892607 prefixEnd_892607 := by exact prefixLift 892607
  have htrace : WordTrace (prefixWord ++ tailWord_892607) baseStart_892607 baseEnd_892607 := by
    simpa [prefixWord, tailWord_892607, baseEnd_892607] using wordTrace_append hprefix tailTrace_892607
  have hstable : (prefixWord ++ tailWord_892607).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_892607).length < 2 ^ (prefixWord ++ tailWord_892607).sum := by decide
  have hdescent : baseEnd_892607 < baseStart_892607 := by decide
  rcases family_descends (prefixWord ++ tailWord_892607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_892641 : List Nat := [1, 2, 3, 1, 5, 2, 1, 6]
def baseStart_892641 : Nat := 118140960795 + 892641 * 2 ^ 59
def prefixEnd_892641 : Nat := 4983230072969 + 3 ^ 40 * 892641 * 2
def baseEnd_892641 : Nat := 67904279245947743952937

theorem tailTrace_892641 : CollatzResearch.WordTrace tailWord_892641 prefixEnd_892641 67904279245947743952937 := by
  unfold tailWord_892641
  simp only [CollatzResearch.WordTrace]
  refine ⟨32557291959121582790669777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21704861306081055193779851 32557291959121582790669777)
  ·
    refine ⟨24417968969341187093002333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32557291959121582790669777 24417968969341187093002333)
    ·
      refine ⟨9156738363502945159875875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24417968969341187093002333 9156738363502945159875875)
      ·
        refine ⟨13735107545254417739813813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9156738363502945159875875 13735107545254417739813813)
        ·
          refine ⟨1287666332367601663107545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13735107545254417739813813 1287666332367601663107545)
          ·
            refine ⟨965749749275701247330659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1287666332367601663107545 965749749275701247330659)
            ·
              refine ⟨1448624623913551870995989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 965749749275701247330659 1448624623913551870995989)
              ·
                refine ⟨67904279245947743952937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1448624623913551870995989 67904279245947743952937)
                ·
                  rfl

theorem cell21_892641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 1, 6].length) (baseStart_892641 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_892641 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_892641 prefixEnd_892641 := by exact prefixLift 892641
  have htrace : WordTrace (prefixWord ++ tailWord_892641) baseStart_892641 baseEnd_892641 := by
    simpa [prefixWord, tailWord_892641, baseEnd_892641] using wordTrace_append hprefix tailTrace_892641
  have hstable : (prefixWord ++ tailWord_892641).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_892641).length < 2 ^ (prefixWord ++ tailWord_892641).sum := by decide
  have hdescent : baseEnd_892641 < baseStart_892641 := by decide
  rcases family_descends (prefixWord ++ tailWord_892641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_892678 : List Nat := [6, 2, 2, 1, 1, 1, 1, 1, 6]
def baseStart_892678 : Nat := 118140960795 + 892678 * 2 ^ 59
def prefixEnd_892678 : Nat := 4983230072969 + 3 ^ 40 * 892678 * 2
def baseEnd_892678 : Nat := 203721281641939389742069

theorem tailTrace_892678 : CollatzResearch.WordTrace tailWord_892678 prefixEnd_892678 203721281641939389742069 := by
  unfold tailWord_892678
  simp only [CollatzResearch.WordTrace]
  refine ⟨1017457545624610565930209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 21705760973325025406511125 1017457545624610565930209)
  ·
    refine ⟨763093159218457924447657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1017457545624610565930209 763093159218457924447657)
    ·
      refine ⟨572319869413843443335743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 763093159218457924447657 572319869413843443335743)
      ·
        refine ⟨858479804120765165003615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 572319869413843443335743 858479804120765165003615)
        ·
          refine ⟨1287719706181147747505423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 858479804120765165003615 1287719706181147747505423)
          ·
            refine ⟨1931579559271721621258135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1287719706181147747505423 1931579559271721621258135)
            ·
              refine ⟨2897369338907582431887203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1931579559271721621258135 2897369338907582431887203)
              ·
                refine ⟨4346054008361373647830805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2897369338907582431887203 4346054008361373647830805)
                ·
                  refine ⟨203721281641939389742069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4346054008361373647830805 203721281641939389742069)
                  ·
                    rfl

theorem cell21_892678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 1, 1, 6].length) (baseStart_892678 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_892678 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_892678 prefixEnd_892678 := by exact prefixLift 892678
  have htrace : WordTrace (prefixWord ++ tailWord_892678) baseStart_892678 baseEnd_892678 := by
    simpa [prefixWord, tailWord_892678, baseEnd_892678] using wordTrace_append hprefix tailTrace_892678
  have hstable : (prefixWord ++ tailWord_892678).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_892678).length < 2 ^ (prefixWord ++ tailWord_892678).sum := by decide
  have hdescent : baseEnd_892678 < baseStart_892678 := by decide
  rcases family_descends (prefixWord ++ tailWord_892678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_892686 : List Nat := [4, 1, 1, 2, 1, 1, 5, 2, 4]
def baseStart_892686 : Nat := 118140960795 + 892686 * 2 ^ 59
def prefixEnd_892686 : Nat := 4983230072969 + 3 ^ 40 * 892686 * 2
def baseEnd_892686 : Nat := 203723107350933153608719

theorem tailTrace_892686 : CollatzResearch.WordTrace tailWord_892686 prefixEnd_892686 203723107350933153608719 := by
  unfold tailWord_892686
  simp only [CollatzResearch.WordTrace]
  refine ⟨4069866655494819434507239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21705955495972370317371941 4069866655494819434507239)
  ·
    refine ⟨6104799983242229151760859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4069866655494819434507239 6104799983242229151760859)
    ·
      refine ⟨9157199974863343727641289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6104799983242229151760859 9157199974863343727641289)
      ·
        refine ⟨6867899981147507795730967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9157199974863343727641289 6867899981147507795730967)
        ·
          refine ⟨10301849971721261693596451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6867899981147507795730967 10301849971721261693596451)
          ·
            refine ⟨15452774957581892540394677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10301849971721261693596451 15452774957581892540394677)
            ·
              refine ⟨1448697652273302425662001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15452774957581892540394677 1448697652273302425662001)
              ·
                refine ⟨1086523239204976819246501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1448697652273302425662001 1086523239204976819246501)
                ·
                  refine ⟨203723107350933153608719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1086523239204976819246501 203723107350933153608719)
                  ·
                    rfl

theorem cell21_892686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 5, 2, 4].length) (baseStart_892686 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_892686 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_892686 prefixEnd_892686 := by exact prefixLift 892686
  have htrace : WordTrace (prefixWord ++ tailWord_892686) baseStart_892686 baseEnd_892686 := by
    simpa [prefixWord, tailWord_892686, baseEnd_892686] using wordTrace_append hprefix tailTrace_892686
  have hstable : (prefixWord ++ tailWord_892686).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_892686).length < 2 ^ (prefixWord ++ tailWord_892686).sum := by decide
  have hdescent : baseEnd_892686 < baseStart_892686 := by decide
  rcases family_descends (prefixWord ++ tailWord_892686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_892745 : List Nat := [1, 2, 1, 1, 2, 4, 2, 4, 4]
def baseStart_892745 : Nat := 118140960795 + 892745 * 2 ^ 59
def prefixEnd_892745 : Nat := 4983230072969 + 3 ^ 40 * 892745 * 2
def baseEnd_892745 : Nat := 203736571954762162125265

theorem tailTrace_892745 : CollatzResearch.WordTrace tailWord_892745 prefixEnd_892745 203736571954762162125265 := by
  unfold tailWord_892745
  simp only [CollatzResearch.WordTrace]
  refine ⟨32561085150744808552455689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21707390100496539034970459 32561085150744808552455689)
  ·
    refine ⟨24420813863058606414341767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32561085150744808552455689 24420813863058606414341767)
    ·
      refine ⟨36631220794587909621512651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24420813863058606414341767 36631220794587909621512651)
      ·
        refine ⟨54946831191881864432268977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36631220794587909621512651 54946831191881864432268977)
        ·
          refine ⟨41210123393911398324201733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54946831191881864432268977 41210123393911398324201733)
          ·
            refine ⟨7726898136358387185787825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41210123393911398324201733 7726898136358387185787825)
            ·
              refine ⟨5795173602268790389340869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7726898136358387185787825 5795173602268790389340869)
              ·
                refine ⟨1086595050425398198001413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5795173602268790389340869 1086595050425398198001413)
                ·
                  refine ⟨203736571954762162125265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1086595050425398198001413 203736571954762162125265)
                  ·
                    rfl

theorem cell21_892745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 4, 4].length) (baseStart_892745 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_892745 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_892745 prefixEnd_892745 := by exact prefixLift 892745
  have htrace : WordTrace (prefixWord ++ tailWord_892745) baseStart_892745 baseEnd_892745 := by
    simpa [prefixWord, tailWord_892745, baseEnd_892745] using wordTrace_append hprefix tailTrace_892745
  have hstable : (prefixWord ++ tailWord_892745).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_892745).length < 2 ^ (prefixWord ++ tailWord_892745).sum := by decide
  have hdescent : baseEnd_892745 < baseStart_892745 := by decide
  rcases family_descends (prefixWord ++ tailWord_892745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_892748 : List Nat := [2, 2, 1, 3, 4, 2, 1, 1, 5]
def baseStart_892748 : Nat := 118140960795 + 892748 * 2 ^ 59
def prefixEnd_892748 : Nat := 4983230072969 + 3 ^ 40 * 892748 * 2
def baseEnd_892748 : Nat := 203737256595634823575259

theorem tailTrace_892748 : CollatzResearch.WordTrace tailWord_892748 prefixEnd_892748 203737256595634823575259 := by
  unfold tailWord_892748
  simp only [CollatzResearch.WordTrace]
  refine ⟨16280597284866970032407449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21707463046489293376543265 16280597284866970032407449)
  ·
    refine ⟨12210447963650227524305587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16280597284866970032407449 12210447963650227524305587)
    ·
      refine ⟨18315671945475341286458381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12210447963650227524305587 18315671945475341286458381)
      ·
        refine ⟨6868376979553252982421893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18315671945475341286458381 6868376979553252982421893)
        ·
          refine ⟨1287820683666234934204105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6868376979553252982421893 1287820683666234934204105)
          ·
            refine ⟨965865512749676200653079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1287820683666234934204105 965865512749676200653079)
            ·
              refine ⟨1448798269124514300979619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 965865512749676200653079 1448798269124514300979619)
              ·
                refine ⟨2173197403686771451469429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1448798269124514300979619 2173197403686771451469429)
                ·
                  refine ⟨203737256595634823575259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2173197403686771451469429 203737256595634823575259)
                  ·
                    rfl

theorem cell21_892748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 1, 1, 5].length) (baseStart_892748 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_892748 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_892748 prefixEnd_892748 := by exact prefixLift 892748
  have htrace : WordTrace (prefixWord ++ tailWord_892748) baseStart_892748 baseEnd_892748 := by
    simpa [prefixWord, tailWord_892748, baseEnd_892748] using wordTrace_append hprefix tailTrace_892748
  have hstable : (prefixWord ++ tailWord_892748).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_892748).length < 2 ^ (prefixWord ++ tailWord_892748).sum := by decide
  have hdescent : baseEnd_892748 < baseStart_892748 := by decide
  rcases family_descends (prefixWord ++ tailWord_892748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_892810 : List Nat := [3, 1, 2, 4, 3, 1, 1, 6]
def baseStart_892810 : Nat := 118140960795 + 892810 * 2 ^ 59
def prefixEnd_892810 : Nat := 4983230072969 + 3 ^ 40 * 892810 * 2
def baseEnd_892810 : Nat := 67917135280112164513933

theorem tailTrace_892810 : CollatzResearch.WordTrace tailWord_892810 prefixEnd_892810 67917135280112164513933 := by
  unfold tailWord_892810
  simp only [CollatzResearch.WordTrace]
  refine ⟨8140863973877331163392971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21708970597006216435714589 8140863973877331163392971)
  ·
    refine ⟨12211295960815996745089457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8140863973877331163392971 12211295960815996745089457)
    ·
      refine ⟨9158471970611997558817093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12211295960815996745089457 9158471970611997558817093)
      ·
        refine ⟨1717213494489749542278205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9158471970611997558817093 1717213494489749542278205)
        ·
          refine ⟨643955060433656078354327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1717213494489749542278205 643955060433656078354327)
          ·
            refine ⟨965932590650484117531491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 643955060433656078354327 965932590650484117531491)
            ·
              refine ⟨1448898885975726176297237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 965932590650484117531491 1448898885975726176297237)
              ·
                refine ⟨67917135280112164513933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1448898885975726176297237 67917135280112164513933)
                ·
                  rfl

theorem cell21_892810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 1, 6].length) (baseStart_892810 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_892810 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_892810 prefixEnd_892810 := by exact prefixLift 892810
  have htrace : WordTrace (prefixWord ++ tailWord_892810) baseStart_892810 baseEnd_892810 := by
    simpa [prefixWord, tailWord_892810, baseEnd_892810] using wordTrace_append hprefix tailTrace_892810
  have hstable : (prefixWord ++ tailWord_892810).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_892810).length < 2 ^ (prefixWord ++ tailWord_892810).sum := by decide
  have hdescent : baseEnd_892810 < baseStart_892810 := by decide
  rcases family_descends (prefixWord ++ tailWord_892810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_892821 : List Nat := [1, 3, 2, 1, 1, 3, 1, 5, 4]
def baseStart_892821 : Nat := 118140960795 + 892821 * 2 ^ 59
def prefixEnd_892821 : Nat := 4983230072969 + 3 ^ 40 * 892821 * 2
def baseEnd_892821 : Nat := 203753916190202918858443

theorem tailTrace_892821 : CollatzResearch.WordTrace tailWord_892821 prefixEnd_892821 203753916190202918858443 := by
  unfold tailWord_892821
  simp only [CollatzResearch.WordTrace]
  refine ⟨32563857098469473532222317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21709238065646315688148211 32563857098469473532222317)
  ·
    refine ⟨12211446411926052574583369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32563857098469473532222317 12211446411926052574583369)
    ·
      refine ⟨9158584808944539430937527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12211446411926052574583369 9158584808944539430937527)
      ·
        refine ⟨13737877213416809146406291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9158584808944539430937527 13737877213416809146406291)
        ·
          refine ⟨20606815820125213719609437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13737877213416809146406291 20606815820125213719609437)
          ·
            refine ⟨7727555932546955144853539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20606815820125213719609437 7727555932546955144853539)
            ·
              refine ⟨11591333898820432717280309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7727555932546955144853539 11591333898820432717280309)
              ·
                refine ⟨1086687553014415567245029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11591333898820432717280309 1086687553014415567245029)
                ·
                  refine ⟨203753916190202918858443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1086687553014415567245029 203753916190202918858443)
                  ·
                    rfl

theorem cell21_892821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 5, 4].length) (baseStart_892821 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_892821 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_892821 prefixEnd_892821 := by exact prefixLift 892821
  have htrace : WordTrace (prefixWord ++ tailWord_892821) baseStart_892821 baseEnd_892821 := by
    simpa [prefixWord, tailWord_892821, baseEnd_892821] using wordTrace_append hprefix tailTrace_892821
  have hstable : (prefixWord ++ tailWord_892821).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_892821).length < 2 ^ (prefixWord ++ tailWord_892821).sum := by decide
  have hdescent : baseEnd_892821 < baseStart_892821 := by decide
  rcases family_descends (prefixWord ++ tailWord_892821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_892824 : List Nat := [2, 1, 2, 6, 1, 1, 1, 2, 5]
def baseStart_892824 : Nat := 118140960795 + 892824 * 2 ^ 59
def prefixEnd_892824 : Nat := 4983230072969 + 3 ^ 40 * 892824 * 2
def baseEnd_892824 : Nat := 203754600831075580308437

theorem tailTrace_892824 : CollatzResearch.WordTrace tailWord_892824 prefixEnd_892824 203754600831075580308437 := by
  unfold tailWord_892824
  simp only [CollatzResearch.WordTrace]
  refine ⟨16281983258729302522290763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21709311011639070029721017 16281983258729302522290763)
  ·
    refine ⟨24422974888093953783436145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16281983258729302522290763 24422974888093953783436145)
    ·
      refine ⟨18317231166070465337577109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24422974888093953783436145 18317231166070465337577109)
      ·
        refine ⟨858620210909553062698927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 18317231166070465337577109 858620210909553062698927)
        ·
          refine ⟨1287930316364329594048391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 858620210909553062698927 1287930316364329594048391)
          ·
            refine ⟨1931895474546494391072587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1287930316364329594048391 1931895474546494391072587)
            ·
              refine ⟨2897843211819741586608881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1931895474546494391072587 2897843211819741586608881)
              ·
                refine ⟨2173382408864806189956661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2897843211819741586608881 2173382408864806189956661)
                ·
                  refine ⟨203754600831075580308437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2173382408864806189956661 203754600831075580308437)
                  ·
                    rfl

theorem cell21_892824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 1, 2, 5].length) (baseStart_892824 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_892824 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_892824 prefixEnd_892824 := by exact prefixLift 892824
  have htrace : WordTrace (prefixWord ++ tailWord_892824) baseStart_892824 baseEnd_892824 := by
    simpa [prefixWord, tailWord_892824, baseEnd_892824] using wordTrace_append hprefix tailTrace_892824
  have hstable : (prefixWord ++ tailWord_892824).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_892824).length < 2 ^ (prefixWord ++ tailWord_892824).sum := by decide
  have hdescent : baseEnd_892824 < baseStart_892824 := by decide
  rcases family_descends (prefixWord ++ tailWord_892824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_892892 : List Nat := [2, 2, 6, 1, 2, 1, 1, 3, 3]
def baseStart_892892 : Nat := 118140960795 + 892892 * 2 ^ 59
def prefixEnd_892892 : Nat := 4983230072969 + 3 ^ 40 * 892892 * 2
def baseEnd_892892 : Nat := 203770119357522573174965

theorem tailTrace_892892 : CollatzResearch.WordTrace tailWord_892892 prefixEnd_892892 203770119357522573174965 := by
  unfold tailWord_892892
  simp only [CollatzResearch.WordTrace]
  refine ⟨16283223340606126329028465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21710964454141501772037953 16283223340606126329028465)
  ·
    refine ⟨12212417505454594746771349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16283223340606126329028465 12212417505454594746771349)
    ·
      refine ⟨572457070568184128754907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 12212417505454594746771349 572457070568184128754907)
      ·
        refine ⟨858685605852276193132361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 572457070568184128754907 858685605852276193132361)
        ·
          refine ⟨644014204389207144849271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 858685605852276193132361 644014204389207144849271)
          ·
            refine ⟨966021306583810717273907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 644014204389207144849271 966021306583810717273907)
            ·
              refine ⟨1449031959875716075910861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 966021306583810717273907 1449031959875716075910861)
              ·
                refine ⟨543386984953393528466573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1449031959875716075910861 543386984953393528466573)
                ·
                  refine ⟨203770119357522573174965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 543386984953393528466573 203770119357522573174965)
                  ·
                    rfl

theorem cell21_892892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 1, 3, 3].length) (baseStart_892892 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_892892 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_892892 prefixEnd_892892 := by exact prefixLift 892892
  have htrace : WordTrace (prefixWord ++ tailWord_892892) baseStart_892892 baseEnd_892892 := by
    simpa [prefixWord, tailWord_892892, baseEnd_892892] using wordTrace_append hprefix tailTrace_892892
  have hstable : (prefixWord ++ tailWord_892892).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_892892).length < 2 ^ (prefixWord ++ tailWord_892892).sum := by decide
  have hdescent : baseEnd_892892 < baseStart_892892 := by decide
  rcases family_descends (prefixWord ++ tailWord_892892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_892942 : List Nat := [4, 1, 1, 2, 2, 1, 2, 1, 7]
def baseStart_892942 : Nat := 118140960795 + 892942 * 2 ^ 59
def prefixEnd_892942 : Nat := 4983230072969 + 3 ^ 40 * 892942 * 2
def baseEnd_892942 : Nat := 203781530038733597341529

theorem tailTrace_892942 : CollatzResearch.WordTrace tailWord_892942 prefixEnd_892942 203781530038733597341529 := by
  unfold tailWord_892942
  simp only [CollatzResearch.WordTrace]
  refine ⟨4071033791378888899672135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21712180220687407464918053 4071033791378888899672135)
  ·
    refine ⟨6106550687068333349508203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4071033791378888899672135 6106550687068333349508203)
    ·
      refine ⟨9159826030602500024262305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6106550687068333349508203 9159826030602500024262305)
      ·
        refine ⟨6869869522951875018196729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9159826030602500024262305 6869869522951875018196729)
        ·
          refine ⟨5152402142213906263647547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6869869522951875018196729 5152402142213906263647547)
          ·
            refine ⟨7728603213320859395471321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5152402142213906263647547 7728603213320859395471321)
            ·
              refine ⟨5796452409990644546603491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7728603213320859395471321 5796452409990644546603491)
              ·
                refine ⟨8694678614985966819905237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5796452409990644546603491 8694678614985966819905237)
                ·
                  refine ⟨203781530038733597341529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8694678614985966819905237 203781530038733597341529)
                  ·
                    rfl

theorem cell21_892942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 1, 7].length) (baseStart_892942 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_892942 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_892942 prefixEnd_892942 := by exact prefixLift 892942
  have htrace : WordTrace (prefixWord ++ tailWord_892942) baseStart_892942 baseEnd_892942 := by
    simpa [prefixWord, tailWord_892942, baseEnd_892942] using wordTrace_append hprefix tailTrace_892942
  have hstable : (prefixWord ++ tailWord_892942).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_892942).length < 2 ^ (prefixWord ++ tailWord_892942).sum := by decide
  have hdescent : baseEnd_892942 < baseStart_892942 := by decide
  rcases family_descends (prefixWord ++ tailWord_892942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_892959 : List Nat := [1, 1, 2, 4, 1, 2, 2, 5, 3]
def baseStart_892959 : Nat := 118140960795 + 892959 * 2 ^ 59
def prefixEnd_892959 : Nat := 4983230072969 + 3 ^ 40 * 892959 * 2
def baseEnd_892959 : Nat := 203785409670345345558161

theorem tailTrace_892959 : CollatzResearch.WordTrace tailWord_892959 prefixEnd_892959 203785409670345345558161 := by
  unfold tailWord_892959
  simp only [CollatzResearch.WordTrace]
  refine ⟨32568890371969523100745931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21712593581313015400497287 32568890371969523100745931)
  ·
    refine ⟨48853335557954284651118897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32568890371969523100745931 48853335557954284651118897)
    ·
      refine ⟨36640001668465713488339173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48853335557954284651118897 36640001668465713488339173)
      ·
        refine ⟨6870000312837321279063595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36640001668465713488339173 6870000312837321279063595)
        ·
          refine ⟨10305000469255981918595393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6870000312837321279063595 10305000469255981918595393)
          ·
            refine ⟨7728750351941986438946545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10305000469255981918595393 7728750351941986438946545)
            ·
              refine ⟨5796562763956489829209909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7728750351941986438946545 5796562763956489829209909)
              ·
                refine ⟨543427759120920921488429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5796562763956489829209909 543427759120920921488429)
                ·
                  refine ⟨203785409670345345558161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 543427759120920921488429 203785409670345345558161)
                  ·
                    rfl

theorem cell21_892959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 5, 3].length) (baseStart_892959 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_892959 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_892959 prefixEnd_892959 := by exact prefixLift 892959
  have htrace : WordTrace (prefixWord ++ tailWord_892959) baseStart_892959 baseEnd_892959 := by
    simpa [prefixWord, tailWord_892959, baseEnd_892959] using wordTrace_append hprefix tailTrace_892959
  have hstable : (prefixWord ++ tailWord_892959).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_892959).length < 2 ^ (prefixWord ++ tailWord_892959).sum := by decide
  have hdescent : baseEnd_892959 < baseStart_892959 := by decide
  rcases family_descends (prefixWord ++ tailWord_892959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_892976 : List Nat := [2, 1, 1, 1, 2, 5, 4, 2, 3]
def baseStart_892976 : Nat := 118140960795 + 892976 * 2 ^ 59
def prefixEnd_892976 : Nat := 4983230072969 + 3 ^ 40 * 892976 * 2
def baseEnd_892976 : Nat := 203789289301957093774793

theorem tailTrace_892976 : CollatzResearch.WordTrace tailWord_892976 prefixEnd_892976 203789289301957093774793 := by
  unfold tailWord_892976
  simp only [CollatzResearch.WordTrace]
  refine ⟨16284755206453967502057391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21713006941938623336076521 16284755206453967502057391)
  ·
    refine ⟨24427132809680951253086087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16284755206453967502057391 24427132809680951253086087)
    ·
      refine ⟨36640699214521426879629131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24427132809680951253086087 36640699214521426879629131)
      ·
        refine ⟨54961048821782140319443697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36640699214521426879629131 54961048821782140319443697)
        ·
          refine ⟨41220786616336605239582773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54961048821782140319443697 41220786616336605239582773)
          ·
            refine ⟨3864448745281556741210885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 41220786616336605239582773 3864448745281556741210885)
            ·
              refine ⟨724584139740291888977041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3864448745281556741210885 724584139740291888977041)
              ·
                refine ⟨543438104805218916732781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 724584139740291888977041 543438104805218916732781)
                ·
                  refine ⟨203789289301957093774793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 543438104805218916732781 203789289301957093774793)
                  ·
                    rfl

theorem cell21_892976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 4, 2, 3].length) (baseStart_892976 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_892976 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_892976 prefixEnd_892976 := by exact prefixLift 892976
  have htrace : WordTrace (prefixWord ++ tailWord_892976) baseStart_892976 baseEnd_892976 := by
    simpa [prefixWord, tailWord_892976, baseEnd_892976] using wordTrace_append hprefix tailTrace_892976
  have hstable : (prefixWord ++ tailWord_892976).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_892976).length < 2 ^ (prefixWord ++ tailWord_892976).sum := by decide
  have hdescent : baseEnd_892976 < baseStart_892976 := by decide
  rcases family_descends (prefixWord ++ tailWord_892976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_893080 : List Nat := [2, 1, 2, 4, 3, 2, 7]
def baseStart_893080 : Nat := 118140960795 + 893080 * 2 ^ 59
def prefixEnd_893080 : Nat := 4983230072969 + 3 ^ 40 * 893080 * 2
def baseEnd_893080 : Nat := 22645891502097336004583

theorem tailTrace_893080 : CollatzResearch.WordTrace tailWord_893080 prefixEnd_893080 22645891502097336004583 := by
  unfold tailWord_893080
  simp only [CollatzResearch.WordTrace]
  refine ⟨16286651802265580382950347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21715535736354107177267129 16286651802265580382950347)
  ·
    refine ⟨24429977703398370574425521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16286651802265580382950347 24429977703398370574425521)
    ·
      refine ⟨18322483277548777930819141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24429977703398370574425521 18322483277548777930819141)
      ·
        refine ⟨3435465614540395862028589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18322483277548777930819141 3435465614540395862028589)
        ·
          refine ⟨1288299605452648448260721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3435465614540395862028589 1288299605452648448260721)
          ·
            refine ⟨966224704089486336195541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1288299605452648448260721 966224704089486336195541)
            ·
              refine ⟨22645891502097336004583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 966224704089486336195541 22645891502097336004583)
              ·
                rfl

theorem cell21_893080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 7].length) (baseStart_893080 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_893080 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_893080 prefixEnd_893080 := by exact prefixLift 893080
  have htrace : WordTrace (prefixWord ++ tailWord_893080) baseStart_893080 baseEnd_893080 := by
    simpa [prefixWord, tailWord_893080, baseEnd_893080] using wordTrace_append hprefix tailTrace_893080
  have hstable : (prefixWord ++ tailWord_893080).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_893080).length < 2 ^ (prefixWord ++ tailWord_893080).sum := by decide
  have hdescent : baseEnd_893080 < baseStart_893080 := by decide
  rcases family_descends (prefixWord ++ tailWord_893080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_893086 : List Nat := [4, 3, 1, 1, 3, 1, 3, 2, 3]
def baseStart_893086 : Nat := 118140960795 + 893086 * 2 ^ 59
def prefixEnd_893086 : Nat := 4983230072969 + 3 ^ 40 * 893086 * 2
def baseEnd_893086 : Nat := 203814392800621346941235

theorem tailTrace_893086 : CollatzResearch.WordTrace tailWord_893086 prefixEnd_893086 203814392800621346941235 := by
  unfold tailWord_893086
  simp only [CollatzResearch.WordTrace]
  refine ⟨4071690305313677973827389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21715681628339615860412741 4071690305313677973827389)
  ·
    refine ⟨1526883864492629240185271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4071690305313677973827389 1526883864492629240185271)
    ·
      refine ⟨2290325796738943860277907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1526883864492629240185271 2290325796738943860277907)
      ·
        refine ⟨3435488695108415790416861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2290325796738943860277907 3435488695108415790416861)
        ·
          refine ⟨1288308260665655921406323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3435488695108415790416861 1288308260665655921406323)
          ·
            refine ⟨1932462390998483882109485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1288308260665655921406323 1932462390998483882109485)
            ·
              refine ⟨724673396624431455791057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1932462390998483882109485 724673396624431455791057)
              ·
                refine ⟨543505047468323591843293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 724673396624431455791057 543505047468323591843293)
                ·
                  refine ⟨203814392800621346941235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 543505047468323591843293 203814392800621346941235)
                  ·
                    rfl

theorem cell21_893086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 3, 2, 3].length) (baseStart_893086 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_893086 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_893086 prefixEnd_893086 := by exact prefixLift 893086
  have htrace : WordTrace (prefixWord ++ tailWord_893086) baseStart_893086 baseEnd_893086 := by
    simpa [prefixWord, tailWord_893086, baseEnd_893086] using wordTrace_append hprefix tailTrace_893086
  have hstable : (prefixWord ++ tailWord_893086).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_893086).length < 2 ^ (prefixWord ++ tailWord_893086).sum := by decide
  have hdescent : baseEnd_893086 < baseStart_893086 := by decide
  rcases family_descends (prefixWord ++ tailWord_893086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_893170 : List Nat := [3, 2, 1, 3, 2, 1, 1, 1, 7]
def baseStart_893170 : Nat := 118140960795 + 893170 * 2 ^ 59
def prefixEnd_893170 : Nat := 4983230072969 + 3 ^ 40 * 893170 * 2
def baseEnd_893170 : Nat := 203833562745055867541063

theorem tailTrace_893170 : CollatzResearch.WordTrace tailWord_893170 prefixEnd_893170 203833562745055867541063 := by
  unfold tailWord_893170
  simp only [CollatzResearch.WordTrace]
  refine ⟨8144146543551276534169241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21717724116136737424451309 8144146543551276534169241)
  ·
    refine ⟨6108109907663457400626931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8144146543551276534169241 6108109907663457400626931)
    ·
      refine ⟨9162164861495186100940397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6108109907663457400626931 9162164861495186100940397)
      ·
        refine ⟨3435811823060694787852649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9162164861495186100940397 3435811823060694787852649)
        ·
          refine ⟨2576858867295521090889487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3435811823060694787852649 2576858867295521090889487)
          ·
            refine ⟨3865288300943281636334231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2576858867295521090889487 3865288300943281636334231)
            ·
              refine ⟨5797932451414922454501347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3865288300943281636334231 5797932451414922454501347)
              ·
                refine ⟨8696898677122383681752021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5797932451414922454501347 8696898677122383681752021)
                ·
                  refine ⟨203833562745055867541063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8696898677122383681752021 203833562745055867541063)
                  ·
                    rfl

theorem cell21_893170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 1, 7].length) (baseStart_893170 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_893170 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_893170 prefixEnd_893170 := by exact prefixLift 893170
  have htrace : WordTrace (prefixWord ++ tailWord_893170) baseStart_893170 baseEnd_893170 := by
    simpa [prefixWord, tailWord_893170, baseEnd_893170] using wordTrace_append hprefix tailTrace_893170
  have hstable : (prefixWord ++ tailWord_893170).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_893170).length < 2 ^ (prefixWord ++ tailWord_893170).sum := by decide
  have hdescent : baseEnd_893170 < baseStart_893170 := by decide
  rcases family_descends (prefixWord ++ tailWord_893170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_893187 : List Nat := [1, 1, 1, 3, 2, 3, 4, 3, 3]
def baseStart_893187 : Nat := 118140960795 + 893187 * 2 ^ 59
def prefixEnd_893187 : Nat := 4983230072969 + 3 ^ 40 * 893187 * 2
def baseEnd_893187 : Nat := 203837442376667615757695

theorem tailTrace_893187 : CollatzResearch.WordTrace tailWord_893187 prefixEnd_893187 203837442376667615757695 := by
  unfold tailWord_893187
  simp only [CollatzResearch.WordTrace]
  refine ⟨32577206215143518040045815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21718137476762345360030543 32577206215143518040045815)
  ·
    refine ⟨48865809322715277060068723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32577206215143518040045815 48865809322715277060068723)
    ·
      refine ⟨73298713984072915590103085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48865809322715277060068723 73298713984072915590103085)
      ·
        refine ⟨27487017744027343346288657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73298713984072915590103085 27487017744027343346288657)
        ·
          refine ⟨20615263308020507509716493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27487017744027343346288657 20615263308020507509716493)
          ·
            refine ⟨7730723740507690316143685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20615263308020507509716493 7730723740507690316143685)
            ·
              refine ⟨1449510701345191934276941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7730723740507690316143685 1449510701345191934276941)
              ·
                refine ⟨543566513004446975353853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1449510701345191934276941 543566513004446975353853)
                ·
                  refine ⟨203837442376667615757695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 543566513004446975353853 203837442376667615757695)
                  ·
                    rfl

theorem cell21_893187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 4, 3, 3].length) (baseStart_893187 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_893187 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_893187 prefixEnd_893187 := by exact prefixLift 893187
  have htrace : WordTrace (prefixWord ++ tailWord_893187) baseStart_893187 baseEnd_893187 := by
    simpa [prefixWord, tailWord_893187, baseEnd_893187] using wordTrace_append hprefix tailTrace_893187
  have hstable : (prefixWord ++ tailWord_893187).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_893187).length < 2 ^ (prefixWord ++ tailWord_893187).sum := by decide
  have hdescent : baseEnd_893187 < baseStart_893187 := by decide
  rcases family_descends (prefixWord ++ tailWord_893187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_893201 : List Nat := [1, 2, 2, 1, 1, 5, 3, 2, 4]
def baseStart_893201 : Nat := 118140960795 + 893201 * 2 ^ 59
def prefixEnd_893201 : Nat := 4983230072969 + 3 ^ 40 * 893201 * 2
def baseEnd_893201 : Nat := 203840637367406702524333

theorem tailTrace_893201 : CollatzResearch.WordTrace tailWord_893201 prefixEnd_893201 203840637367406702524333 := by
  unfold tailWord_893201
  simp only [CollatzResearch.WordTrace]
  refine ⟨32577716837092798431055457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21718477891395198954036971 32577716837092798431055457)
  ·
    refine ⟨24433287627819598823291593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32577716837092798431055457 24433287627819598823291593)
    ·
      refine ⟨18324965720864699117468695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24433287627819598823291593 18324965720864699117468695)
      ·
        refine ⟨27487448581297048676203043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18324965720864699117468695 27487448581297048676203043)
        ·
          refine ⟨41231172871945573014304565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27487448581297048676203043 41231172871945573014304565)
          ·
            refine ⟨3865422456744897470091053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 41231172871945573014304565 3865422456744897470091053)
            ·
              refine ⟨1449533421279336551284145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3865422456744897470091053 1449533421279336551284145)
              ·
                refine ⟨1087150065959502413463109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1449533421279336551284145 1087150065959502413463109)
                ·
                  refine ⟨203840637367406702524333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1087150065959502413463109 203840637367406702524333)
                  ·
                    rfl

theorem cell21_893201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 3, 2, 4].length) (baseStart_893201 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_893201 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_893201 prefixEnd_893201 := by exact prefixLift 893201
  have htrace : WordTrace (prefixWord ++ tailWord_893201) baseStart_893201 baseEnd_893201 := by
    simpa [prefixWord, tailWord_893201, baseEnd_893201] using wordTrace_append hprefix tailTrace_893201
  have hstable : (prefixWord ++ tailWord_893201).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_893201).length < 2 ^ (prefixWord ++ tailWord_893201).sum := by decide
  have hdescent : baseEnd_893201 < baseStart_893201 := by decide
  rcases family_descends (prefixWord ++ tailWord_893201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_893249 : List Nat := [1, 2, 5, 2, 3, 1, 7]
def baseStart_893249 : Nat := 118140960795 + 893249 * 2 ^ 59
def prefixEnd_893249 : Nat := 4983230072969 + 3 ^ 40 * 893249 * 2
def baseEnd_893249 : Nat := 22650176846818809524915

theorem tailTrace_893249 : CollatzResearch.WordTrace tailWord_893249 prefixEnd_893249 22650176846818809524915 := by
  unfold tailWord_893249
  simp only [CollatzResearch.WordTrace]
  refine ⟨32579467540918902628802801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21719645027279268419201867 32579467540918902628802801)
  ·
    refine ⟨24434600655689176971602101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32579467540918902628802801 24434600655689176971602101)
    ·
      refine ⟨2290743811470860341087697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 24434600655689176971602101 2290743811470860341087697)
      ·
        refine ⟨1718057858603145255815773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2290743811470860341087697 1718057858603145255815773)
        ·
          refine ⟨644271696976179470930915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1718057858603145255815773 644271696976179470930915)
          ·
            refine ⟨966407545464269206396373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 644271696976179470930915 966407545464269206396373)
            ·
              refine ⟨22650176846818809524915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 966407545464269206396373 22650176846818809524915)
              ·
                rfl

theorem cell21_893249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 7].length) (baseStart_893249 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_893249 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_893249 prefixEnd_893249 := by exact prefixLift 893249
  have htrace : WordTrace (prefixWord ++ tailWord_893249) baseStart_893249 baseEnd_893249 := by
    simpa [prefixWord, tailWord_893249, baseEnd_893249] using wordTrace_append hprefix tailTrace_893249
  have hstable : (prefixWord ++ tailWord_893249).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_893249).length < 2 ^ (prefixWord ++ tailWord_893249).sum := by decide
  have hdescent : baseEnd_893249 < baseStart_893249 := by decide
  rcases family_descends (prefixWord ++ tailWord_893249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_893260 : List Nat := [2, 2, 1, 3, 2, 1, 1, 3, 6]
def baseStart_893260 : Nat := 118140960795 + 893260 * 2 ^ 59
def prefixEnd_893260 : Nat := 4983230072969 + 3 ^ 40 * 893260 * 2
def baseEnd_893260 : Nat := 203854101971235711040879

theorem tailTrace_893260 : CollatzResearch.WordTrace tailWord_893260 prefixEnd_893260 203854101971235711040879 := by
  unfold tailWord_893260
  simp only [CollatzResearch.WordTrace]
  refine ⟨16289934371939525753726617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21719912495919367671635489 16289934371939525753726617)
  ·
    refine ⟨12217450778954644315294963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16289934371939525753726617 12217450778954644315294963)
    ·
      refine ⟨18326176168431966472942445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12217450778954644315294963 18326176168431966472942445)
      ·
        refine ⟨6872316063161987427353417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18326176168431966472942445 6872316063161987427353417)
        ·
          refine ⟨5154237047371490570515063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6872316063161987427353417 5154237047371490570515063)
          ·
            refine ⟨7731355571057235855772595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5154237047371490570515063 7731355571057235855772595)
            ·
              refine ⟨11597033356585853783658893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7731355571057235855772595 11597033356585853783658893)
              ·
                refine ⟨4348887508719695168872085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11597033356585853783658893 4348887508719695168872085)
                ·
                  refine ⟨203854101971235711040879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4348887508719695168872085 203854101971235711040879)
                  ·
                    rfl

theorem cell21_893260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 3, 6].length) (baseStart_893260 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_893260 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_893260 prefixEnd_893260 := by exact prefixLift 893260
  have htrace : WordTrace (prefixWord ++ tailWord_893260) baseStart_893260 baseEnd_893260 := by
    simpa [prefixWord, tailWord_893260, baseEnd_893260] using wordTrace_append hprefix tailTrace_893260
  have hstable : (prefixWord ++ tailWord_893260).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_893260).length < 2 ^ (prefixWord ++ tailWord_893260).sum := by decide
  have hdescent : baseEnd_893260 < baseStart_893260 := by decide
  rcases family_descends (prefixWord ++ tailWord_893260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_893460 : List Nat := [2, 4, 3, 1, 1, 1, 2, 7]
def baseStart_893460 : Nat := 118140960795 + 893460 * 2 ^ 59
def prefixEnd_893460 : Nat := 4983230072969 + 3 ^ 40 * 893460 * 2
def baseEnd_893460 : Nat := 67966581565359935902379

theorem tailTrace_893460 : CollatzResearch.WordTrace tailWord_893460 prefixEnd_893460 67966581565359935902379 := by
  unfold tailWord_893460
  simp only [CollatzResearch.WordTrace]
  refine ⟨16293581671577242832366917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21724775562102990443155889 16293581671577242832366917)
  ·
    refine ⟨3055046563420733031068797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16293581671577242832366917 3055046563420733031068797)
    ·
      refine ⟨1145642461282774886650799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3055046563420733031068797 1145642461282774886650799)
      ·
        refine ⟨1718463691924162329976199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1145642461282774886650799 1718463691924162329976199)
        ·
          refine ⟨2577695537886243494964299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1718463691924162329976199 2577695537886243494964299)
          ·
            refine ⟨3866543306829365242446449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2577695537886243494964299 3866543306829365242446449)
            ·
              refine ⟨2899907480122023931834837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3866543306829365242446449 2899907480122023931834837)
              ·
                refine ⟨67966581565359935902379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2899907480122023931834837 67966581565359935902379)
                ·
                  rfl

theorem cell21_893460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 2, 7].length) (baseStart_893460 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_893460 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_893460 prefixEnd_893460 := by exact prefixLift 893460
  have htrace : WordTrace (prefixWord ++ tailWord_893460) baseStart_893460 baseEnd_893460 := by
    simpa [prefixWord, tailWord_893460, baseEnd_893460] using wordTrace_append hprefix tailTrace_893460
  have hstable : (prefixWord ++ tailWord_893460).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_893460).length < 2 ^ (prefixWord ++ tailWord_893460).sum := by decide
  have hdescent : baseEnd_893460 < baseStart_893460 := by decide
  rcases family_descends (prefixWord ++ tailWord_893460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_893488 : List Nat := [2, 1, 1, 1, 2, 3, 3, 4, 4]
def baseStart_893488 : Nat := 118140960795 + 893488 * 2 ^ 59
def prefixEnd_893488 : Nat := 4983230072969 + 3 ^ 40 * 893488 * 2
def baseEnd_893488 : Nat := 203906134677557981240413

theorem tailTrace_893488 : CollatzResearch.WordTrace tailWord_893488 prefixEnd_893488 203906134677557981240413 := by
  unfold tailWord_893488
  simp only [CollatzResearch.WordTrace]
  refine ⟨16294092293526523223376559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21725456391368697631168745 16294092293526523223376559)
  ·
    refine ⟨24441138440289784835064839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16294092293526523223376559 24441138440289784835064839)
    ·
      refine ⟨36661707660434677252597259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24441138440289784835064839 36661707660434677252597259)
      ·
        refine ⟨54992561490652015878895889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36661707660434677252597259 54992561490652015878895889)
        ·
          refine ⟨41244421117989011909171917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54992561490652015878895889 41244421117989011909171917)
          ·
            refine ⟨15466657919245879465939469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41244421117989011909171917 15466657919245879465939469)
            ·
              refine ⟨5799996719717204799727301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15466657919245879465939469 5799996719717204799727301)
              ·
                refine ⟨1087499384946975899948869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5799996719717204799727301 1087499384946975899948869)
                ·
                  refine ⟨203906134677557981240413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1087499384946975899948869 203906134677557981240413)
                  ·
                    rfl

theorem cell21_893488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 4, 4].length) (baseStart_893488 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_893488 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_893488 prefixEnd_893488 := by exact prefixLift 893488
  have htrace : WordTrace (prefixWord ++ tailWord_893488) baseStart_893488 baseEnd_893488 := by
    simpa [prefixWord, tailWord_893488, baseEnd_893488] using wordTrace_append hprefix tailTrace_893488
  have hstable : (prefixWord ++ tailWord_893488).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_893488).length < 2 ^ (prefixWord ++ tailWord_893488).sum := by decide
  have hdescent : baseEnd_893488 < baseStart_893488 := by decide
  rcases family_descends (prefixWord ++ tailWord_893488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_893505 : List Nat := [1, 2, 5, 1, 1, 2, 2, 3, 4]
def baseStart_893505 : Nat := 118140960795 + 893505 * 2 ^ 59
def prefixEnd_893505 : Nat := 4983230072969 + 3 ^ 40 * 893505 * 2
def baseEnd_893505 : Nat := 203910014309169729457045

theorem tailTrace_893505 : CollatzResearch.WordTrace tailWord_893505 prefixEnd_893505 203910014309169729457045 := by
  unfold tailWord_893505
  simp only [CollatzResearch.WordTrace]
  refine ⟨32588804627991458350121969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21725869751994305566747979 32588804627991458350121969)
  ·
    refine ⟨24441603470993593762591477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32588804627991458350121969 24441603470993593762591477)
    ·
      refine ⟨2291400325405649415242951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 24441603470993593762591477 2291400325405649415242951)
      ·
        refine ⟨3437100488108474122864427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2291400325405649415242951 3437100488108474122864427)
        ·
          refine ⟨5155650732162711184296641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3437100488108474122864427 5155650732162711184296641)
          ·
            refine ⟨3866738049122033388222481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5155650732162711184296641 3866738049122033388222481)
            ·
              refine ⟨2900053536841525041166861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3866738049122033388222481 2900053536841525041166861)
              ·
                refine ⟨1087520076315571890437573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2900053536841525041166861 1087520076315571890437573)
                ·
                  refine ⟨203910014309169729457045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1087520076315571890437573 203910014309169729457045)
                  ·
                    rfl

theorem cell21_893505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 2, 3, 4].length) (baseStart_893505 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_893505 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_893505 prefixEnd_893505 := by exact prefixLift 893505
  have htrace : WordTrace (prefixWord ++ tailWord_893505) baseStart_893505 baseEnd_893505 := by
    simpa [prefixWord, tailWord_893505, baseEnd_893505] using wordTrace_append hprefix tailTrace_893505
  have hstable : (prefixWord ++ tailWord_893505).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_893505).length < 2 ^ (prefixWord ++ tailWord_893505).sum := by decide
  have hdescent : baseEnd_893505 < baseStart_893505 := by decide
  rcases family_descends (prefixWord ++ tailWord_893505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_893550 : List Nat := [4, 1, 2, 2, 2, 1, 1, 3, 5]
def baseStart_893550 : Nat := 118140960795 + 893550 * 2 ^ 59
def prefixEnd_893550 : Nat := 4983230072969 + 3 ^ 40 * 893550 * 2
def baseEnd_893550 : Nat := 203920283922259651206953

theorem tailTrace_893550 : CollatzResearch.WordTrace tailWord_893550 prefixEnd_893550 203920283922259651206953 := by
  unfold tailWord_893550
  simp only [CollatzResearch.WordTrace]
  refine ⟨4073805739103553879438763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21726963941885620690340069 4073805739103553879438763)
  ·
    refine ⟨6110708608655330819158145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4073805739103553879438763 6110708608655330819158145)
    ·
      refine ⟨4583031456491498114368609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6110708608655330819158145 4583031456491498114368609)
      ·
        refine ⟨3437273592368623585776457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4583031456491498114368609 3437273592368623585776457)
        ·
          refine ⟨2577955194276467689332343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3437273592368623585776457 2577955194276467689332343)
          ·
            refine ⟨3866932791414701533998515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2577955194276467689332343 3866932791414701533998515)
            ·
              refine ⟨5800399187122052300997773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3866932791414701533998515 5800399187122052300997773)
              ·
                refine ⟨2175149695170769612874165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5800399187122052300997773 2175149695170769612874165)
                ·
                  refine ⟨203920283922259651206953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2175149695170769612874165 203920283922259651206953)
                  ·
                    rfl

theorem cell21_893550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 3, 5].length) (baseStart_893550 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_893550 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_893550 prefixEnd_893550 := by exact prefixLift 893550
  have htrace : WordTrace (prefixWord ++ tailWord_893550) baseStart_893550 baseEnd_893550 := by
    simpa [prefixWord, tailWord_893550, baseEnd_893550] using wordTrace_append hprefix tailTrace_893550
  have hstable : (prefixWord ++ tailWord_893550).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_893550).length < 2 ^ (prefixWord ++ tailWord_893550).sum := by decide
  have hdescent : baseEnd_893550 < baseStart_893550 := by decide
  rcases family_descends (prefixWord ++ tailWord_893550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_893564 : List Nat := [2, 2, 2, 1, 1, 2, 2, 5, 4]
def baseStart_893564 : Nat := 118140960795 + 893564 * 2 ^ 59
def prefixEnd_893564 : Nat := 4983230072969 + 3 ^ 40 * 893564 * 2
def baseEnd_893564 : Nat := 203923478912998737973591

theorem tailTrace_893564 : CollatzResearch.WordTrace tailWord_893564 prefixEnd_893564 203923478912998737973591 := by
  unfold tailWord_893564
  simp only [CollatzResearch.WordTrace]
  refine ⟨16295478267388855713259873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21727304356518474284346497 16295478267388855713259873)
  ·
    refine ⟨12221608700541641784944905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16295478267388855713259873 12221608700541641784944905)
    ·
      refine ⟨9166206525406231338708679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12221608700541641784944905 9166206525406231338708679)
      ·
        refine ⟨13749309788109347008063019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9166206525406231338708679 13749309788109347008063019)
        ·
          refine ⟨20623964682164020512094529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13749309788109347008063019 20623964682164020512094529)
          ·
            refine ⟨15467973511623015384070897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20623964682164020512094529 15467973511623015384070897)
            ·
              refine ⟨11600980133717261538053173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15467973511623015384070897 11600980133717261538053173)
              ·
                refine ⟨1087591887535993269192485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11600980133717261538053173 1087591887535993269192485)
                ·
                  refine ⟨203923478912998737973591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1087591887535993269192485 203923478912998737973591)
                  ·
                    rfl

theorem cell21_893564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 5, 4].length) (baseStart_893564 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_893564 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_893564 prefixEnd_893564 := by exact prefixLift 893564
  have htrace : WordTrace (prefixWord ++ tailWord_893564) baseStart_893564 baseEnd_893564 := by
    simpa [prefixWord, tailWord_893564, baseEnd_893564] using wordTrace_append hprefix tailTrace_893564
  have hstable : (prefixWord ++ tailWord_893564).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_893564).length < 2 ^ (prefixWord ++ tailWord_893564).sum := by decide
  have hdescent : baseEnd_893564 < baseStart_893564 := by decide
  rcases family_descends (prefixWord ++ tailWord_893564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_893570 : List Nat := [3, 4, 3, 1, 1, 1, 1, 7]
def baseStart_893570 : Nat := 118140960795 + 893570 * 2 ^ 59
def prefixEnd_893570 : Nat := 4983230072969 + 3 ^ 40 * 893570 * 2
def baseEnd_893570 : Nat := 67974949398248020291193

theorem tailTrace_893570 : CollatzResearch.WordTrace tailWord_893570 prefixEnd_893570 67974949398248020291193 := by
  unfold tailWord_893570
  simp only [CollatzResearch.WordTrace]
  refine ⟨8147793843188993612809541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21727450248503982967492109 8147793843188993612809541)
  ·
    refine ⟨1527711345597936302401789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8147793843188993612809541 1527711345597936302401789)
    ·
      refine ⟨572891754599226113400671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1527711345597936302401789 572891754599226113400671)
      ·
        refine ⟨859337631898839170101007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 572891754599226113400671 859337631898839170101007)
        ·
          refine ⟨1289006447848258755151511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 859337631898839170101007 1289006447848258755151511)
          ·
            refine ⟨1933509671772388132727267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1289006447848258755151511 1933509671772388132727267)
            ·
              refine ⟨2900264507658582199090901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1933509671772388132727267 2900264507658582199090901)
              ·
                refine ⟨67974949398248020291193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2900264507658582199090901 67974949398248020291193)
                ·
                  rfl

theorem cell21_893570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 1, 7].length) (baseStart_893570 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_893570 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_893570 prefixEnd_893570 := by exact prefixLift 893570
  have htrace : WordTrace (prefixWord ++ tailWord_893570) baseStart_893570 baseEnd_893570 := by
    simpa [prefixWord, tailWord_893570, baseEnd_893570] using wordTrace_append hprefix tailTrace_893570
  have hstable : (prefixWord ++ tailWord_893570).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_893570).length < 2 ^ (prefixWord ++ tailWord_893570).sum := by decide
  have hdescent : baseEnd_893570 < baseStart_893570 := by decide
  rcases family_descends (prefixWord ++ tailWord_893570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_893660 : List Nat := [2, 2, 5, 1, 1, 2, 1, 4, 3]
def baseStart_893660 : Nat := 118140960795 + 893660 * 2 ^ 59
def prefixEnd_893660 : Nat := 4983230072969 + 3 ^ 40 * 893660 * 2
def baseEnd_893660 : Nat := 203945387420923904373395

theorem tailTrace_893660 : CollatzResearch.WordTrace tailWord_893660 prefixEnd_893660 203945387420923904373395 := by
  unfold tailWord_893660
  simp only [CollatzResearch.WordTrace]
  refine ⟨16297228971214959911007217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21729638628286613214676289 16297228971214959911007217)
  ·
    refine ⟨12222921728411219933255413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16297228971214959911007217 12222921728411219933255413)
    ·
      refine ⟨1145898912038551868742695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12222921728411219933255413 1145898912038551868742695)
      ·
        refine ⟨1718848368057827803114043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1145898912038551868742695 1718848368057827803114043)
        ·
          refine ⟨2578272552086741704671065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1718848368057827803114043 2578272552086741704671065)
          ·
            refine ⟨1933704414065056278503299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2578272552086741704671065 1933704414065056278503299)
            ·
              refine ⟨2900556621097584417754949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1933704414065056278503299 2900556621097584417754949)
              ·
                refine ⟨543854366455797078329053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2900556621097584417754949 543854366455797078329053)
                ·
                  refine ⟨203945387420923904373395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 543854366455797078329053 203945387420923904373395)
                  ·
                    rfl

theorem cell21_893660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 1, 4, 3].length) (baseStart_893660 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_893660 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_893660 prefixEnd_893660 := by exact prefixLift 893660
  have htrace : WordTrace (prefixWord ++ tailWord_893660) baseStart_893660 baseEnd_893660 := by
    simpa [prefixWord, tailWord_893660, baseEnd_893660] using wordTrace_append hprefix tailTrace_893660
  have hstable : (prefixWord ++ tailWord_893660).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_893660).length < 2 ^ (prefixWord ++ tailWord_893660).sum := by decide
  have hdescent : baseEnd_893660 < baseStart_893660 := by decide
  rcases family_descends (prefixWord ++ tailWord_893660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_893699 : List Nat := [1, 1, 1, 3, 2, 2, 1, 4, 6]
def baseStart_893699 : Nat := 118140960795 + 893699 * 2 ^ 59
def prefixEnd_893699 : Nat := 4983230072969 + 3 ^ 40 * 893699 * 2
def baseEnd_893699 : Nat := 203954287752268503223315

theorem tailTrace_893699 : CollatzResearch.WordTrace tailWord_893699 prefixEnd_893699 203954287752268503223315 := by
  unfold tailWord_893699
  simp only [CollatzResearch.WordTrace]
  refine ⟨32595880389288629482684151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21730586926192419655122767 32595880389288629482684151)
  ·
    refine ⟨48893820583932944224026227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32595880389288629482684151 48893820583932944224026227)
    ·
      refine ⟨73340730875899416336039341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48893820583932944224026227 73340730875899416336039341)
      ·
        refine ⟨27502774078462281126014753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73340730875899416336039341 27502774078462281126014753)
        ·
          refine ⟨20627080558846710844511065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27502774078462281126014753 20627080558846710844511065)
          ·
            refine ⟨15470310419135033133383299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20627080558846710844511065 15470310419135033133383299)
            ·
              refine ⟨23205465628702549700074949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15470310419135033133383299 23205465628702549700074949)
              ·
                refine ⟨4351024805381728068764053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23205465628702549700074949 4351024805381728068764053)
                ·
                  refine ⟨203954287752268503223315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4351024805381728068764053 203954287752268503223315)
                  ·
                    rfl

theorem cell21_893699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 4, 6].length) (baseStart_893699 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_893699 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_893699 prefixEnd_893699 := by exact prefixLift 893699
  have htrace : WordTrace (prefixWord ++ tailWord_893699) baseStart_893699 baseEnd_893699 := by
    simpa [prefixWord, tailWord_893699, baseEnd_893699] using wordTrace_append hprefix tailTrace_893699
  have hstable : (prefixWord ++ tailWord_893699).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_893699).length < 2 ^ (prefixWord ++ tailWord_893699).sum := by decide
  have hdescent : baseEnd_893699 < baseStart_893699 := by decide
  rcases family_descends (prefixWord ++ tailWord_893699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_893733 : List Nat := [1, 3, 1, 2, 3, 1, 5, 1, 4]
def baseStart_893733 : Nat := 118140960795 + 893733 * 2 ^ 59
def prefixEnd_893733 : Nat := 4983230072969 + 3 ^ 40 * 893733 * 2
def baseEnd_893733 : Nat := 203962047015491999656579

theorem tailTrace_893733 : CollatzResearch.WordTrace tailWord_893733 prefixEnd_893733 203962047015491999656579 := by
  unfold tailWord_893733
  simp only [CollatzResearch.WordTrace]
  refine ⟨32597120471165453289421853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21731413647443635526281235 32597120471165453289421853)
  ·
    refine ⟨12223920176687044983533195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32597120471165453289421853 12223920176687044983533195)
    ·
      refine ⟨18335880265030567475299793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12223920176687044983533195 18335880265030567475299793)
      ·
        refine ⟨13751910198772925606474845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18335880265030567475299793 13751910198772925606474845)
        ·
          refine ⟨5156966324539847102428067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13751910198772925606474845 5156966324539847102428067)
          ·
            refine ⟨7735449486809770653642101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5156966324539847102428067 7735449486809770653642101)
            ·
              refine ⟨725198389388415998778947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7735449486809770653642101 725198389388415998778947)
              ·
                refine ⟨1087797584082623998168421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 725198389388415998778947 1087797584082623998168421)
                ·
                  refine ⟨203962047015491999656579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1087797584082623998168421 203962047015491999656579)
                  ·
                    rfl

theorem cell21_893733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 5, 1, 4].length) (baseStart_893733 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_893733 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_893733 prefixEnd_893733 := by exact prefixLift 893733
  have htrace : WordTrace (prefixWord ++ tailWord_893733) baseStart_893733 baseEnd_893733 := by
    simpa [prefixWord, tailWord_893733, baseEnd_893733] using wordTrace_append hprefix tailTrace_893733
  have hstable : (prefixWord ++ tailWord_893733).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_893733).length < 2 ^ (prefixWord ++ tailWord_893733).sum := by decide
  have hdescent : baseEnd_893733 < baseStart_893733 := by decide
  rcases family_descends (prefixWord ++ tailWord_893733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_893747 : List Nat := [1, 1, 1, 2, 6, 1, 4, 5]
def baseStart_893747 : Nat := 118140960795 + 893747 * 2 ^ 59
def prefixEnd_893747 : Nat := 4983230072969 + 3 ^ 40 * 893747 * 2
def baseEnd_893747 : Nat := 67988414002077028807739

theorem tailTrace_893747 : CollatzResearch.WordTrace tailWord_893747 prefixEnd_893747 67988414002077028807739 := by
  unfold tailWord_893747
  simp only [CollatzResearch.WordTrace]
  refine ⟨32597631093114733680431495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21731754062076489120287663 32597631093114733680431495)
  ·
    refine ⟨48896446639672100520647243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32597631093114733680431495 48896446639672100520647243)
    ·
      refine ⟨73344669959508150780970865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48896446639672100520647243 73344669959508150780970865)
      ·
        refine ⟨55008502469631113085728149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73344669959508150780970865 55008502469631113085728149)
        ·
          refine ⟨2578523553263958425893507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 55008502469631113085728149 2578523553263958425893507)
          ·
            refine ⟨3867785329895937638840261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2578523553263958425893507 3867785329895937638840261)
            ·
              refine ⟨725209749355488307282549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3867785329895937638840261 725209749355488307282549)
              ·
                refine ⟨67988414002077028807739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 725209749355488307282549 67988414002077028807739)
                ·
                  rfl

theorem cell21_893747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 4, 5].length) (baseStart_893747 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_893747 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_893747 prefixEnd_893747 := by exact prefixLift 893747
  have htrace : WordTrace (prefixWord ++ tailWord_893747) baseStart_893747 baseEnd_893747 := by
    simpa [prefixWord, tailWord_893747, baseEnd_893747] using wordTrace_append hprefix tailTrace_893747
  have hstable : (prefixWord ++ tailWord_893747).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_893747).length < 2 ^ (prefixWord ++ tailWord_893747).sum := by decide
  have hdescent : baseEnd_893747 < baseStart_893747 := by decide
  rcases family_descends (prefixWord ++ tailWord_893747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_893792 : List Nat := [2, 1, 1, 3, 3, 1, 3, 3, 4]
def baseStart_893792 : Nat := 118140960795 + 893792 * 2 ^ 59
def prefixEnd_893792 : Nat := 4983230072969 + 3 ^ 40 * 893792 * 2
def baseEnd_893792 : Nat := 203975511619321008173125

theorem tailTrace_893792 : CollatzResearch.WordTrace tailWord_893792 prefixEnd_893792 203975511619321008173125 := by
  unfold tailWord_893792
  simp only [CollatzResearch.WordTrace]
  refine ⟨16299636188975853182909815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21732848251967804243879753 16299636188975853182909815)
  ·
    refine ⟨24449454283463779774364723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16299636188975853182909815 24449454283463779774364723)
    ·
      refine ⟨36674181425195669661547085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24449454283463779774364723 36674181425195669661547085)
      ·
        refine ⟨13752818034448376123080157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36674181425195669661547085 13752818034448376123080157)
        ·
          refine ⟨5157306762918141046155059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13752818034448376123080157 5157306762918141046155059)
          ·
            refine ⟨7735960144377211569232589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5157306762918141046155059 7735960144377211569232589)
            ·
              refine ⟨2900985054141454338462221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7735960144377211569232589 2900985054141454338462221)
              ·
                refine ⟨1087869395303045376923333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2900985054141454338462221 1087869395303045376923333)
                ·
                  refine ⟨203975511619321008173125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1087869395303045376923333 203975511619321008173125)
                  ·
                    rfl

theorem cell21_893792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 3, 3, 4].length) (baseStart_893792 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_893792 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_893792 prefixEnd_893792 := by exact prefixLift 893792
  have htrace : WordTrace (prefixWord ++ tailWord_893792) baseStart_893792 baseEnd_893792 := by
    simpa [prefixWord, tailWord_893792, baseEnd_893792] using wordTrace_append hprefix tailTrace_893792
  have hstable : (prefixWord ++ tailWord_893792).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_893792).length < 2 ^ (prefixWord ++ tailWord_893792).sum := by decide
  have hdescent : baseEnd_893792 < baseStart_893792 := by decide
  rcases family_descends (prefixWord ++ tailWord_893792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_893913 : List Nat := [1, 2, 1, 2, 5, 1, 2, 2, 5]
def baseStart_893913 : Nat := 118140960795 + 893913 * 2 ^ 59
def prefixEnd_893913 : Nat := 4983230072969 + 3 ^ 40 * 893913 * 2
def baseEnd_893913 : Nat := 204003125467851686656211

theorem tailTrace_893913 : CollatzResearch.WordTrace tailWord_893913 prefixEnd_893913 204003125467851686656211 := by
  unfold tailWord_893913
  simp only [CollatzResearch.WordTrace]
  refine ⟨32603685610513344030974393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21735790407008896020649595 32603685610513344030974393)
  ·
    refine ⟨24452764207885008023230795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32603685610513344030974393 24452764207885008023230795)
    ·
      refine ⟨36679146311827512034846193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24452764207885008023230795 36679146311827512034846193)
      ·
        refine ⟨27509359733870634026134645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36679146311827512034846193 27509359733870634026134645)
        ·
          refine ⟨2579002475050371939950123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 27509359733870634026134645 2579002475050371939950123)
          ·
            refine ⟨3868503712575557909925185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2579002475050371939950123 3868503712575557909925185)
            ·
              refine ⟨2901377784431668432443889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3868503712575557909925185 2901377784431668432443889)
              ·
                refine ⟨2176033338323751324332917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2901377784431668432443889 2176033338323751324332917)
                ·
                  refine ⟨204003125467851686656211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2176033338323751324332917 204003125467851686656211)
                  ·
                    rfl

theorem cell21_893913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 2, 2, 5].length) (baseStart_893913 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_893913 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_893913 prefixEnd_893913 := by exact prefixLift 893913
  have htrace : WordTrace (prefixWord ++ tailWord_893913) baseStart_893913 baseEnd_893913 := by
    simpa [prefixWord, tailWord_893913, baseEnd_893913] using wordTrace_append hprefix tailTrace_893913
  have hstable : (prefixWord ++ tailWord_893913).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_893913).length < 2 ^ (prefixWord ++ tailWord_893913).sum := by decide
  have hdescent : baseEnd_893913 < baseStart_893913 := by decide
  rcases family_descends (prefixWord ++ tailWord_893913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_894048 : List Nat := [2, 1, 1, 3, 2, 2, 1, 2, 7]
def baseStart_894048 : Nat := 118140960795 + 894048 * 2 ^ 59
def prefixEnd_894048 : Nat := 4983230072969 + 3 ^ 40 * 894048 * 2
def baseEnd_894048 : Nat := 204033934307121451905935

theorem tailTrace_894048 : CollatzResearch.WordTrace tailWord_894048 prefixEnd_894048 204033934307121451905935 := by
  unfold tailWord_894048
  simp only [CollatzResearch.WordTrace]
  refine ⟨16304304732512131043569399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21739072976682841391425865 16304304732512131043569399)
  ·
    refine ⟨24456457098768196565354099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16304304732512131043569399 24456457098768196565354099)
    ·
      refine ⟨36684685648152294848031149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24456457098768196565354099 36684685648152294848031149)
      ·
        refine ⟨13756757118057110568011681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36684685648152294848031149 13756757118057110568011681)
        ·
          refine ⟨10317567838542832926008761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13756757118057110568011681 10317567838542832926008761)
          ·
            refine ⟨7738175878907124694506571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10317567838542832926008761 7738175878907124694506571)
            ·
              refine ⟨11607263818360687041759857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7738175878907124694506571 11607263818360687041759857)
              ·
                refine ⟨8705447863770515281319893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11607263818360687041759857 8705447863770515281319893)
                ·
                  refine ⟨204033934307121451905935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8705447863770515281319893 204033934307121451905935)
                  ·
                    rfl

theorem cell21_894048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 2, 7].length) (baseStart_894048 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_894048 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_894048 prefixEnd_894048 := by exact prefixLift 894048
  have htrace : WordTrace (prefixWord ++ tailWord_894048) baseStart_894048 baseEnd_894048 := by
    simpa [prefixWord, tailWord_894048, baseEnd_894048] using wordTrace_append hprefix tailTrace_894048
  have hstable : (prefixWord ++ tailWord_894048).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_894048).length < 2 ^ (prefixWord ++ tailWord_894048).sum := by decide
  have hdescent : baseEnd_894048 < baseStart_894048 := by decide
  rcases family_descends (prefixWord ++ tailWord_894048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_894124 : List Nat := [2, 2, 1, 1, 1, 1, 1, 7, 5]
def baseStart_894124 : Nat := 118140960795 + 894124 * 2 ^ 59
def prefixEnd_894124 : Nat := 4983230072969 + 3 ^ 40 * 894124 * 2
def baseEnd_894124 : Nat := 204051278542562208639113

theorem tailTrace_894124 : CollatzResearch.WordTrace tailWord_894124 prefixEnd_894124 204051278542562208639113 := by
  unfold tailWord_894124
  simp only [CollatzResearch.WordTrace]
  refine ⟨16305690706374463533452713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21740920941832618044603617 16305690706374463533452713)
  ·
    refine ⟨12229268029780847650089535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16305690706374463533452713 12229268029780847650089535)
    ·
      refine ⟨18343902044671271475134303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12229268029780847650089535 18343902044671271475134303)
      ·
        refine ⟨27515853067006907212701455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18343902044671271475134303 27515853067006907212701455)
        ·
          refine ⟨41273779600510360819052183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27515853067006907212701455 41273779600510360819052183)
          ·
            refine ⟨61910669400765541228578275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41273779600510360819052183 61910669400765541228578275)
            ·
              refine ⟨92866004101148311842867413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61910669400765541228578275 92866004101148311842867413)
              ·
                refine ⟨2176546971120663558817205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 92866004101148311842867413 2176546971120663558817205)
                ·
                  refine ⟨204051278542562208639113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2176546971120663558817205 204051278542562208639113)
                  ·
                    rfl

theorem cell21_894124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 5].length) (baseStart_894124 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_894124 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_894124 prefixEnd_894124 := by exact prefixLift 894124
  have htrace : WordTrace (prefixWord ++ tailWord_894124) baseStart_894124 baseEnd_894124 := by
    simpa [prefixWord, tailWord_894124, baseEnd_894124] using wordTrace_append hprefix tailTrace_894124
  have hstable : (prefixWord ++ tailWord_894124).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_894124).length < 2 ^ (prefixWord ++ tailWord_894124).sum := by decide
  have hdescent : baseEnd_894124 < baseStart_894124 := by decide
  rcases family_descends (prefixWord ++ tailWord_894124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_894186 : List Nat := [3, 1, 3, 1, 1, 3, 3, 6]
def baseStart_894186 : Nat := 118140960795 + 894186 * 2 ^ 59
def prefixEnd_894186 : Nat := 4983230072969 + 3 ^ 40 * 894186 * 2
def baseEnd_894186 : Nat := 68021809262421292868551

theorem tailTrace_894186 : CollatzResearch.WordTrace tailWord_894186 prefixEnd_894186 68021809262421292868551 := by
  unfold tailWord_894186
  simp only [CollatzResearch.WordTrace]
  refine ⟨8153410684631077913915603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21742428492349541103774941 8153410684631077913915603)
  ·
    refine ⟨12230116026946616870873405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8153410684631077913915603 12230116026946616870873405)
    ·
      refine ⟨4586293510104981326577527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12230116026946616870873405 4586293510104981326577527)
      ·
        refine ⟨6879440265157471989866291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4586293510104981326577527 6879440265157471989866291)
        ·
          refine ⟨10319160397736207984799437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6879440265157471989866291 10319160397736207984799437)
          ·
            refine ⟨3869685149151077994299789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10319160397736207984799437 3869685149151077994299789)
            ·
              refine ⟨1451131930931654247862421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3869685149151077994299789 1451131930931654247862421)
              ·
                refine ⟨68021809262421292868551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1451131930931654247862421 68021809262421292868551)
                ·
                  rfl

theorem cell21_894186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 3, 6].length) (baseStart_894186 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_894186 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_894186 prefixEnd_894186 := by exact prefixLift 894186
  have htrace : WordTrace (prefixWord ++ tailWord_894186) baseStart_894186 baseEnd_894186 := by
    simpa [prefixWord, tailWord_894186, baseEnd_894186] using wordTrace_append hprefix tailTrace_894186
  have hstable : (prefixWord ++ tailWord_894186).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_894186).length < 2 ^ (prefixWord ++ tailWord_894186).sum := by decide
  have hdescent : baseEnd_894186 < baseStart_894186 := by decide
  rcases family_descends (prefixWord ++ tailWord_894186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_894231 : List Nat := [1, 1, 3, 4, 1, 1, 3, 1, 6]
def baseStart_894231 : Nat := 118140960795 + 894231 * 2 ^ 59
def prefixEnd_894231 : Nat := 4983230072969 + 3 ^ 40 * 894231 * 2
def baseEnd_894231 : Nat := 204075697400353800355561

theorem tailTrace_894231 : CollatzResearch.WordTrace tailWord_894231 prefixEnd_894231 204075697400353800355561 := by
  unfold tailWord_894231
  simp only [CollatzResearch.WordTrace]
  refine ⟨32615284023361284341050547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21743522682240856227367031 32615284023361284341050547)
  ·
    refine ⟨48922926035041926511575821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32615284023361284341050547 48922926035041926511575821)
    ·
      refine ⟨18346097263140722441840933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48922926035041926511575821 18346097263140722441840933)
      ·
        refine ⟨3439893236838885457845175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18346097263140722441840933 3439893236838885457845175)
        ·
          refine ⟨5159839855258328186767763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3439893236838885457845175 5159839855258328186767763)
          ·
            refine ⟨7739759782887492280151645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5159839855258328186767763 7739759782887492280151645)
            ·
              refine ⟨2902409918582809605056867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7739759782887492280151645 2902409918582809605056867)
              ·
                refine ⟨4353614877874214407585301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2902409918582809605056867 4353614877874214407585301)
                ·
                  refine ⟨204075697400353800355561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4353614877874214407585301 204075697400353800355561)
                  ·
                    rfl

theorem cell21_894231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 3, 1, 6].length) (baseStart_894231 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_894231 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_894231 prefixEnd_894231 := by exact prefixLift 894231
  have htrace : WordTrace (prefixWord ++ tailWord_894231) baseStart_894231 baseEnd_894231 := by
    simpa [prefixWord, tailWord_894231, baseEnd_894231] using wordTrace_append hprefix tailTrace_894231
  have hstable : (prefixWord ++ tailWord_894231).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_894231).length < 2 ^ (prefixWord ++ tailWord_894231).sum := by decide
  have hdescent : baseEnd_894231 < baseStart_894231 := by decide
  rcases family_descends (prefixWord ++ tailWord_894231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_894234 : List Nat := [3, 1, 1, 3, 3, 1, 2, 4, 3]
def baseStart_894234 : Nat := 118140960795 + 894234 * 2 ^ 59
def prefixEnd_894234 : Nat := 4983230072969 + 3 ^ 40 * 894234 * 2
def baseEnd_894234 : Nat := 204076382041226461805555

theorem tailTrace_894234 : CollatzResearch.WordTrace tailWord_894234 prefixEnd_894234 204076382041226461805555 := by
  unfold tailWord_894234
  simp only [CollatzResearch.WordTrace]
  refine ⟨8153848360587603963352439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21743595628233610568939837 8153848360587603963352439)
  ·
    refine ⟨12230772540881405945028659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8153848360587603963352439 12230772540881405945028659)
    ·
      refine ⟨18346158811322108917542989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12230772540881405945028659 18346158811322108917542989)
      ·
        refine ⟨6879809554245790844078621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18346158811322108917542989 6879809554245790844078621)
        ·
          refine ⟨2579928582842171566529483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6879809554245790844078621 2579928582842171566529483)
          ·
            refine ⟨3869892874263257349794225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2579928582842171566529483 3869892874263257349794225)
            ·
              refine ⟨2902419655697443012345669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3869892874263257349794225 2902419655697443012345669)
              ·
                refine ⟨544203685443270564814813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2902419655697443012345669 544203685443270564814813)
                ·
                  refine ⟨204076382041226461805555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 544203685443270564814813 204076382041226461805555)
                  ·
                    rfl

theorem cell21_894234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 2, 4, 3].length) (baseStart_894234 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_894234 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_894234 prefixEnd_894234 := by exact prefixLift 894234
  have htrace : WordTrace (prefixWord ++ tailWord_894234) baseStart_894234 baseEnd_894234 := by
    simpa [prefixWord, tailWord_894234, baseEnd_894234] using wordTrace_append hprefix tailTrace_894234
  have hstable : (prefixWord ++ tailWord_894234).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_894234).length < 2 ^ (prefixWord ++ tailWord_894234).sum := by decide
  have hdescent : baseEnd_894234 < baseStart_894234 := by decide
  rcases family_descends (prefixWord ++ tailWord_894234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_894285 : List Nat := [1, 6, 1, 3, 1, 1, 3, 2, 3]
def baseStart_894285 : Nat := 118140960795 + 894285 * 2 ^ 59
def prefixEnd_894285 : Nat := 4983230072969 + 3 ^ 40 * 894285 * 2
def baseEnd_894285 : Nat := 204088020936061706455451

theorem tailTrace_894285 : CollatzResearch.WordTrace tailWord_894285 prefixEnd_894285 204088020936061706455451 := by
  unfold tailWord_894285
  simp only [CollatzResearch.WordTrace]
  refine ⟨32617253565165651563516309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21744835710110434375677539 32617253565165651563516309)
  ·
    refine ⟨1528933760867139917039827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 32617253565165651563516309 1528933760867139917039827)
    ·
      refine ⟨2293400641300709875559741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1528933760867139917039827 2293400641300709875559741)
      ·
        refine ⟨860025240487766203334903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2293400641300709875559741 860025240487766203334903)
        ·
          refine ⟨1290037860731649305002355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 860025240487766203334903 1290037860731649305002355)
          ·
            refine ⟨1935056791097473957503533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1290037860731649305002355 1935056791097473957503533)
            ·
              refine ⟨725646296661552734063825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1935056791097473957503533 725646296661552734063825)
              ·
                refine ⟨544234722496164550547869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 725646296661552734063825 544234722496164550547869)
                ·
                  refine ⟨204088020936061706455451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 544234722496164550547869 204088020936061706455451)
                  ·
                    rfl

theorem cell21_894285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 3, 2, 3].length) (baseStart_894285 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_894285 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_894285 prefixEnd_894285 := by exact prefixLift 894285
  have htrace : WordTrace (prefixWord ++ tailWord_894285) baseStart_894285 baseEnd_894285 := by
    simpa [prefixWord, tailWord_894285, baseEnd_894285] using wordTrace_append hprefix tailTrace_894285
  have hstable : (prefixWord ++ tailWord_894285).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_894285).length < 2 ^ (prefixWord ++ tailWord_894285).sum := by decide
  have hdescent : baseEnd_894285 < baseStart_894285 := by decide
  rcases family_descends (prefixWord ++ tailWord_894285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_894293 : List Nat := [1, 3, 2, 2, 3, 1, 3, 1, 5]
def baseStart_894293 : Nat := 118140960795 + 894293 * 2 ^ 59
def prefixEnd_894293 : Nat := 4983230072969 + 3 ^ 40 * 894293 * 2
def baseEnd_894293 : Nat := 204089846645055470322101

theorem tailTrace_894293 : CollatzResearch.WordTrace tailWord_894293 prefixEnd_894293 204089846645055470322101 := by
  unfold tailWord_894293
  simp only [CollatzResearch.WordTrace]
  refine ⟨32617545349136668929807533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21745030232757779286538355 32617545349136668929807533)
  ·
    refine ⟨12231579505926250848677825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32617545349136668929807533 12231579505926250848677825)
    ·
      refine ⟨9173684629444688136508369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12231579505926250848677825 9173684629444688136508369)
      ·
        refine ⟨6880263472083516102381277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9173684629444688136508369 6880263472083516102381277)
        ·
          refine ⟨2580098802031318538392979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6880263472083516102381277 2580098802031318538392979)
          ·
            refine ⟨3870148203046977807589469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2580098802031318538392979 3870148203046977807589469)
            ·
              refine ⟨1451305576142616677846051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3870148203046977807589469 1451305576142616677846051)
              ·
                refine ⟨2176958364213925016769077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1451305576142616677846051 2176958364213925016769077)
                ·
                  refine ⟨204089846645055470322101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2176958364213925016769077 204089846645055470322101)
                  ·
                    rfl

theorem cell21_894293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 3, 1, 5].length) (baseStart_894293 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_894293 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_894293 prefixEnd_894293 := by exact prefixLift 894293
  have htrace : WordTrace (prefixWord ++ tailWord_894293) baseStart_894293 baseEnd_894293 := by
    simpa [prefixWord, tailWord_894293, baseEnd_894293] using wordTrace_append hprefix tailTrace_894293
  have hstable : (prefixWord ++ tailWord_894293).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_894293).length < 2 ^ (prefixWord ++ tailWord_894293).sum := by decide
  have hdescent : baseEnd_894293 < baseStart_894293 := by decide
  rcases family_descends (prefixWord ++ tailWord_894293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_894321 : List Nat := [1, 2, 2, 2, 1, 2, 4, 7]
def baseStart_894321 : Nat := 118140960795 + 894321 * 2 ^ 59
def prefixEnd_894321 : Nat := 4983230072969 + 3 ^ 40 * 894321 * 2
def baseEnd_894321 : Nat := 68032078875511214618459

theorem tailTrace_894321 : CollatzResearch.WordTrace tailWord_894321 prefixEnd_894321 68032078875511214618459 := by
  unfold tailWord_894321
  simp only [CollatzResearch.WordTrace]
  refine ⟨32618566593035229711826817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21745711062023486474551211 32618566593035229711826817)
  ·
    refine ⟨24463924944776422283870113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32618566593035229711826817 24463924944776422283870113)
    ·
      refine ⟨18347943708582316712902585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24463924944776422283870113 18347943708582316712902585)
      ·
        refine ⟨13760957781436737534676939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18347943708582316712902585 13760957781436737534676939)
        ·
          refine ⟨20641436672155106302015409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13760957781436737534676939 20641436672155106302015409)
          ·
            refine ⟨15481077504116329726511557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20641436672155106302015409 15481077504116329726511557)
            ·
              refine ⟨2902702032021811823720917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15481077504116329726511557 2902702032021811823720917)
              ·
                refine ⟨68032078875511214618459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2902702032021811823720917 68032078875511214618459)
                ·
                  rfl

theorem cell21_894321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 4, 7].length) (baseStart_894321 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_894321 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_894321 prefixEnd_894321 := by exact prefixLift 894321
  have htrace : WordTrace (prefixWord ++ tailWord_894321) baseStart_894321 baseEnd_894321 := by
    simpa [prefixWord, tailWord_894321, baseEnd_894321] using wordTrace_append hprefix tailTrace_894321
  have hstable : (prefixWord ++ tailWord_894321).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_894321).length < 2 ^ (prefixWord ++ tailWord_894321).sum := by decide
  have hdescent : baseEnd_894321 < baseStart_894321 := by decide
  rcases family_descends (prefixWord ++ tailWord_894321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_894397 : List Nat := [1, 4, 1, 2, 2, 1, 10]
def baseStart_894397 : Nat := 118140960795 + 894397 * 2 ^ 59
def prefixEnd_894397 : Nat := 4983230072969 + 3 ^ 40 * 894397 * 2
def baseEnd_894397 : Nat := 22679286762441600065395

theorem tailTrace_894397 : CollatzResearch.WordTrace tailWord_894397 prefixEnd_894397 22679286762441600065395 := by
  unfold tailWord_894397
  simp only [CollatzResearch.WordTrace]
  refine ⟨32621338540759894691593445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21747559027173263127728963 32621338540759894691593445)
  ·
    refine ⟨6116500976392480254673771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32621338540759894691593445 6116500976392480254673771)
    ·
      refine ⟨9174751464588720382010657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6116500976392480254673771 9174751464588720382010657)
      ·
        refine ⟨6881063598441540286507993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9174751464588720382010657 6881063598441540286507993)
        ·
          refine ⟨5160797698831155214880995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6881063598441540286507993 5160797698831155214880995)
          ·
            refine ⟨7741196548246732822321493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5160797698831155214880995 7741196548246732822321493)
            ·
              refine ⟨22679286762441600065395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 7741196548246732822321493 22679286762441600065395)
              ·
                rfl

theorem cell21_894397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 10].length) (baseStart_894397 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_894397 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_894397 prefixEnd_894397 := by exact prefixLift 894397
  have htrace : WordTrace (prefixWord ++ tailWord_894397) baseStart_894397 baseEnd_894397 := by
    simpa [prefixWord, tailWord_894397, baseEnd_894397] using wordTrace_append hprefix tailTrace_894397
  have hstable : (prefixWord ++ tailWord_894397).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_894397).length < 2 ^ (prefixWord ++ tailWord_894397).sum := by decide
  have hdescent : baseEnd_894397 < baseStart_894397 := by decide
  rcases family_descends (prefixWord ++ tailWord_894397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_894473 : List Nat := [1, 2, 1, 1, 3, 1, 6, 6]
def baseStart_894473 : Nat := 118140960795 + 894473 * 2 ^ 59
def prefixEnd_894473 : Nat := 4983230072969 + 3 ^ 40 * 894473 * 2
def baseEnd_894473 : Nat := 68043641699138385773911

theorem tailTrace_894473 : CollatzResearch.WordTrace tailWord_894473 prefixEnd_894473 68043641699138385773911 := by
  unfold tailWord_894473
  simp only [CollatzResearch.WordTrace]
  refine ⟨32624110488484559671360073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21749406992323039780906715 32624110488484559671360073)
  ·
    refine ⟨24468082866363419753520055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32624110488484559671360073 24468082866363419753520055)
    ·
      refine ⟨36702124299545129630280083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24468082866363419753520055 36702124299545129630280083)
      ·
        refine ⟨55053186449317694445420125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36702124299545129630280083 55053186449317694445420125)
        ·
          refine ⟨20644944918494135417032547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55053186449317694445420125 20644944918494135417032547)
          ·
            refine ⟨30967417377741203125548821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20644944918494135417032547 30967417377741203125548821)
            ·
              refine ⟨1451597689581618896510101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 30967417377741203125548821 1451597689581618896510101)
              ·
                refine ⟨68043641699138385773911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1451597689581618896510101 68043641699138385773911)
                ·
                  rfl

theorem cell21_894473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 6, 6].length) (baseStart_894473 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_894473 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_894473 prefixEnd_894473 := by exact prefixLift 894473
  have htrace : WordTrace (prefixWord ++ tailWord_894473) baseStart_894473 baseEnd_894473 := by
    simpa [prefixWord, tailWord_894473, baseEnd_894473] using wordTrace_append hprefix tailTrace_894473
  have hstable : (prefixWord ++ tailWord_894473).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_894473).length < 2 ^ (prefixWord ++ tailWord_894473).sum := by decide
  have hdescent : baseEnd_894473 < baseStart_894473 := by decide
  rcases family_descends (prefixWord ++ tailWord_894473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_894476 : List Nat := [2, 2, 1, 2, 5, 1, 1, 3, 4]
def baseStart_894476 : Nat := 118140960795 + 894476 * 2 ^ 59
def prefixEnd_894476 : Nat := 4983230072969 + 3 ^ 40 * 894476 * 2
def baseEnd_894476 : Nat := 204131609738287818771727

theorem tailTrace_894476 : CollatzResearch.WordTrace tailWord_894476 prefixEnd_894476 204131609738287818771727 := by
  unfold tailWord_894476
  simp only [CollatzResearch.WordTrace]
  refine ⟨16312109953736845591859641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21749479938315794122479521 16312109953736845591859641)
  ·
    refine ⟨12234082465302634193894731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16312109953736845591859641 12234082465302634193894731)
    ·
      refine ⟨18351123697953951290842097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12234082465302634193894731 18351123697953951290842097)
      ·
        refine ⟨13763342773465463468131573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18351123697953951290842097 13763342773465463468131573)
        ·
          refine ⟨1290313385012387200137335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13763342773465463468131573 1290313385012387200137335)
          ·
            refine ⟨1935470077518580800206003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1290313385012387200137335 1935470077518580800206003)
            ·
              refine ⟨2903205116277871200309005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1935470077518580800206003 2903205116277871200309005)
              ·
                refine ⟨1088701918604201700115877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2903205116277871200309005 1088701918604201700115877)
                ·
                  refine ⟨204131609738287818771727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1088701918604201700115877 204131609738287818771727)
                  ·
                    rfl

theorem cell21_894476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 1, 3, 4].length) (baseStart_894476 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_894476 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_894476 prefixEnd_894476 := by exact prefixLift 894476
  have htrace : WordTrace (prefixWord ++ tailWord_894476) baseStart_894476 baseEnd_894476 := by
    simpa [prefixWord, tailWord_894476, baseEnd_894476] using wordTrace_append hprefix tailTrace_894476
  have hstable : (prefixWord ++ tailWord_894476).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_894476).length < 2 ^ (prefixWord ++ tailWord_894476).sum := by decide
  have hdescent : baseEnd_894476 < baseStart_894476 := by decide
  rcases family_descends (prefixWord ++ tailWord_894476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_894600 : List Nat := [2, 1, 3, 5, 1, 2, 2, 5]
def baseStart_894600 : Nat := 118140960795 + 894600 * 2 ^ 59
def prefixEnd_894600 : Nat := 4983230072969 + 3 ^ 40 * 894600 * 2
def baseEnd_894600 : Nat := 68053302742563719568269

theorem tailTrace_894600 : CollatzResearch.WordTrace tailWord_894600 prefixEnd_894600 68053302742563719568269 := by
  unfold tailWord_894600
  simp only [CollatzResearch.WordTrace]
  refine ⟨16314371279512230180616627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21752495039349640240822169 16314371279512230180616627)
  ·
    refine ⟨24471556919268345270924941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16314371279512230180616627 24471556919268345270924941)
    ·
      refine ⟨9176833844725629476596853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24471556919268345270924941 9176833844725629476596853)
      ·
        refine ⟨860328172943027763430955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9176833844725629476596853 860328172943027763430955)
        ·
          refine ⟨1290492259414541645146433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 860328172943027763430955 1290492259414541645146433)
          ·
            refine ⟨967869194560906233859825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1290492259414541645146433 967869194560906233859825)
            ·
              refine ⟨725901895920679675394869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 967869194560906233859825 725901895920679675394869)
              ·
                refine ⟨68053302742563719568269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 725901895920679675394869 68053302742563719568269)
                ·
                  rfl

theorem cell21_894600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 2, 5].length) (baseStart_894600 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_894600 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_894600 prefixEnd_894600 := by exact prefixLift 894600
  have htrace : WordTrace (prefixWord ++ tailWord_894600) baseStart_894600 baseEnd_894600 := by
    simpa [prefixWord, tailWord_894600, baseEnd_894600] using wordTrace_append hprefix tailTrace_894600
  have hstable : (prefixWord ++ tailWord_894600).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_894600).length < 2 ^ (prefixWord ++ tailWord_894600).sum := by decide
  have hdescent : baseEnd_894600 < baseStart_894600 := by decide
  rcases family_descends (prefixWord ++ tailWord_894600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_894625 : List Nat := [1, 2, 3, 3, 2, 1, 9]
def baseStart_894625 : Nat := 118140960795 + 894625 * 2 ^ 59
def prefixEnd_894625 : Nat := 4983230072969 + 3 ^ 40 * 894625 * 2
def baseEnd_894625 : Nat := 22685068174255185643121

theorem tailTrace_894625 : CollatzResearch.WordTrace tailWord_894625 prefixEnd_894625 22685068174255185643121 := by
  unfold tailWord_894625
  simp only [CollatzResearch.WordTrace]
  refine ⟨32629654383933889630893329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21753102922622593087262219 32629654383933889630893329)
  ·
    refine ⟨24472240787950417223169997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32629654383933889630893329 24472240787950417223169997)
    ·
      refine ⟨9177090295481406458688749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24472240787950417223169997 9177090295481406458688749)
      ·
        refine ⟨3441408860805527422008281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9177090295481406458688749 3441408860805527422008281)
        ·
          refine ⟨2581056645604145566506211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3441408860805527422008281 2581056645604145566506211)
          ·
            refine ⟨3871584968406218349759317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2581056645604145566506211 3871584968406218349759317)
            ·
              refine ⟨22685068174255185643121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3871584968406218349759317 22685068174255185643121)
              ·
                rfl

theorem cell21_894625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 9].length) (baseStart_894625 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_894625 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_894625 prefixEnd_894625 := by exact prefixLift 894625
  have htrace : WordTrace (prefixWord ++ tailWord_894625) baseStart_894625 baseEnd_894625 := by
    simpa [prefixWord, tailWord_894625, baseEnd_894625] using wordTrace_append hprefix tailTrace_894625
  have hstable : (prefixWord ++ tailWord_894625).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_894625).length < 2 ^ (prefixWord ++ tailWord_894625).sum := by decide
  have hdescent : baseEnd_894625 < baseStart_894625 := by decide
  rcases family_descends (prefixWord ++ tailWord_894625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_894687 : List Nat := [1, 1, 2, 3, 2, 2, 4, 2, 4]
def baseStart_894687 : Nat := 118140960795 + 894687 * 2 ^ 59
def prefixEnd_894687 : Nat := 4983230072969 + 3 ^ 40 * 894687 * 2
def baseEnd_894687 : Nat := 204179762812998340754629

theorem tailTrace_894687 : CollatzResearch.WordTrace tailWord_894687 prefixEnd_894687 204179762812998340754629 := by
  unfold tailWord_894687
  simp only [CollatzResearch.WordTrace]
  refine ⟨32631915709709274219650315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21754610473139516146433543 32631915709709274219650315)
  ·
    refine ⟨48947873564563911329475473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32631915709709274219650315 48947873564563911329475473)
    ·
      refine ⟨36710905173422933497106605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48947873564563911329475473 36710905173422933497106605)
      ·
        refine ⟨13766589440033600061414977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36710905173422933497106605 13766589440033600061414977)
        ·
          refine ⟨10324942080025200046061233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13766589440033600061414977 10324942080025200046061233)
          ·
            refine ⟨7743706560018900034545925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10324942080025200046061233 7743706560018900034545925)
            ·
              refine ⟨1451944980003543756477361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7743706560018900034545925 1451944980003543756477361)
              ·
                refine ⟨1088958735002657817358021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1451944980003543756477361 1088958735002657817358021)
                ·
                  refine ⟨204179762812998340754629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1088958735002657817358021 204179762812998340754629)
                  ·
                    rfl

theorem cell21_894687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 4, 2, 4].length) (baseStart_894687 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_894687 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_894687 prefixEnd_894687 := by exact prefixLift 894687
  have htrace : WordTrace (prefixWord ++ tailWord_894687) baseStart_894687 baseEnd_894687 := by
    simpa [prefixWord, tailWord_894687, baseEnd_894687] using wordTrace_append hprefix tailTrace_894687
  have hstable : (prefixWord ++ tailWord_894687).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_894687).length < 2 ^ (prefixWord ++ tailWord_894687).sum := by decide
  have hdescent : baseEnd_894687 < baseStart_894687 := by decide
  rcases family_descends (prefixWord ++ tailWord_894687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_894783 : List Nat := [1, 1, 2, 2, 7, 1, 1, 3, 3]
def baseStart_894783 : Nat := 118140960795 + 894783 * 2 ^ 59
def prefixEnd_894783 : Nat := 4983230072969 + 3 ^ 40 * 894783 * 2
def baseEnd_894783 : Nat := 204201671320923507154433

theorem tailTrace_894783 : CollatzResearch.WordTrace tailWord_894783 prefixEnd_894783 204201671320923507154433 := by
  unfold tailWord_894783
  simp only [CollatzResearch.WordTrace]
  refine ⟨32635417117361482615145003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21756944744907655076763335 32635417117361482615145003)
  ·
    refine ⟨48953125676042223922717505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32635417117361482615145003 48953125676042223922717505)
    ·
      refine ⟨36714844257031667942038129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48953125676042223922717505 36714844257031667942038129)
      ·
        refine ⟨27536133192773750956528597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36714844257031667942038129 27536133192773750956528597)
        ·
          refine ⟨645378121705634788043639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 27536133192773750956528597 645378121705634788043639)
          ·
            refine ⟨968067182558452182065459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 645378121705634788043639 968067182558452182065459)
            ·
              refine ⟨1452100773837678273098189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 968067182558452182065459 1452100773837678273098189)
              ·
                refine ⟨544537790189129352411821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1452100773837678273098189 544537790189129352411821)
                ·
                  refine ⟨204201671320923507154433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 544537790189129352411821 204201671320923507154433)
                  ·
                    rfl

theorem cell21_894783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 1, 3, 3].length) (baseStart_894783 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_894783 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_894783 prefixEnd_894783 := by exact prefixLift 894783
  have htrace : WordTrace (prefixWord ++ tailWord_894783) baseStart_894783 baseEnd_894783 := by
    simpa [prefixWord, tailWord_894783, baseEnd_894783] using wordTrace_append hprefix tailTrace_894783
  have hstable : (prefixWord ++ tailWord_894783).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_894783).length < 2 ^ (prefixWord ++ tailWord_894783).sum := by decide
  have hdescent : baseEnd_894783 < baseStart_894783 := by decide
  rcases family_descends (prefixWord ++ tailWord_894783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_894791 : List Nat := [1, 1, 4, 1, 2, 1, 2, 2, 7]
def baseStart_894791 : Nat := 118140960795 + 894791 * 2 ^ 59
def prefixEnd_894791 : Nat := 4983230072969 + 3 ^ 40 * 894791 * 2
def baseEnd_894791 : Nat := 204203497029917271021083

theorem tailTrace_894791 : CollatzResearch.WordTrace tailWord_894791 prefixEnd_894791 204203497029917271021083 := by
  unfold tailWord_894791
  simp only [CollatzResearch.WordTrace]
  refine ⟨32635708901332499981436227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21757139267554999987624151 32635708901332499981436227)
  ·
    refine ⟨48953563351998749972154341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32635708901332499981436227 48953563351998749972154341)
    ·
      refine ⟨9178793128499765619778939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48953563351998749972154341 9178793128499765619778939)
      ·
        refine ⟨13768189692749648429668409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9178793128499765619778939 13768189692749648429668409)
        ·
          refine ⟨10326142269562236322251307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13768189692749648429668409 10326142269562236322251307)
          ·
            refine ⟨15489213404343354483376961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10326142269562236322251307 15489213404343354483376961)
            ·
              refine ⟨11616910053257515862532721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15489213404343354483376961 11616910053257515862532721)
              ·
                refine ⟨8712682539943136896899541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11616910053257515862532721 8712682539943136896899541)
                ·
                  refine ⟨204203497029917271021083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8712682539943136896899541 204203497029917271021083)
                  ·
                    rfl

theorem cell21_894791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 2, 7].length) (baseStart_894791 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_894791 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_894791 prefixEnd_894791 := by exact prefixLift 894791
  have htrace : WordTrace (prefixWord ++ tailWord_894791) baseStart_894791 baseEnd_894791 := by
    simpa [prefixWord, tailWord_894791, baseEnd_894791] using wordTrace_append hprefix tailTrace_894791
  have hstable : (prefixWord ++ tailWord_894791).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_894791).length < 2 ^ (prefixWord ++ tailWord_894791).sum := by decide
  have hdescent : baseEnd_894791 < baseStart_894791 := by decide
  rcases family_descends (prefixWord ++ tailWord_894791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_894856 : List Nat := [2, 1, 3, 3, 3, 1, 2, 2, 4]
def baseStart_894856 : Nat := 118140960795 + 894856 * 2 ^ 59
def prefixEnd_894856 : Nat := 4983230072969 + 3 ^ 40 * 894856 * 2
def baseEnd_894856 : Nat := 204218330915491602437617

theorem tailTrace_894856 : CollatzResearch.WordTrace tailWord_894856 prefixEnd_894856 204218330915491602437617 := by
  unfold tailWord_894856
  simp only [CollatzResearch.WordTrace]
  refine ⟨16319039823048508041276211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21758719764064677388368281 16319039823048508041276211)
  ·
    refine ⟨24478559734572762061914317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16319039823048508041276211 24478559734572762061914317)
    ·
      refine ⟨9179459900464785773217869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24478559734572762061914317 9179459900464785773217869)
      ·
        refine ⟨3442297462674294664956701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9179459900464785773217869 3442297462674294664956701)
        ·
          refine ⟨1290861548502860499358763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3442297462674294664956701 1290861548502860499358763)
          ·
            refine ⟨1936292322754290749038145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1290861548502860499358763 1936292322754290749038145)
            ·
              refine ⟨1452219242065718061778609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1936292322754290749038145 1452219242065718061778609)
              ·
                refine ⟨1089164431549288546333957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1452219242065718061778609 1089164431549288546333957)
                ·
                  refine ⟨204218330915491602437617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1089164431549288546333957 204218330915491602437617)
                  ·
                    rfl

theorem cell21_894856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 2, 2, 4].length) (baseStart_894856 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_894856 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_894856 prefixEnd_894856 := by exact prefixLift 894856
  have htrace : WordTrace (prefixWord ++ tailWord_894856) baseStart_894856 baseEnd_894856 := by
    simpa [prefixWord, tailWord_894856, baseEnd_894856] using wordTrace_append hprefix tailTrace_894856
  have hstable : (prefixWord ++ tailWord_894856).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_894856).length < 2 ^ (prefixWord ++ tailWord_894856).sum := by decide
  have hdescent : baseEnd_894856 < baseStart_894856 := by decide
  rcases family_descends (prefixWord ++ tailWord_894856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_894884 : List Nat := [2, 3, 1, 2, 1, 4, 1, 2, 5]
def baseStart_894884 : Nat := 118140960795 + 894884 * 2 ^ 59
def prefixEnd_894884 : Nat := 4983230072969 + 3 ^ 40 * 894884 * 2
def baseEnd_894884 : Nat := 204224720896969775970893

theorem tailTrace_894884 : CollatzResearch.WordTrace tailWord_894884 prefixEnd_894884 204224720896969775970893 := by
  unfold tailWord_894884
  simp only [CollatzResearch.WordTrace]
  refine ⟨16319550444997788432285853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21759400593330384576381137 16319550444997788432285853)
  ·
    refine ⟨6119831416874170662107195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16319550444997788432285853 6119831416874170662107195)
    ·
      refine ⟨9179747125311255993160793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6119831416874170662107195 9179747125311255993160793)
      ·
        refine ⟨6884810343983441994870595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9179747125311255993160793 6884810343983441994870595)
        ·
          refine ⟨10327215515975162992305893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6884810343983441994870595 10327215515975162992305893)
          ·
            refine ⟨1936352909245343061057355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10327215515975162992305893 1936352909245343061057355)
            ·
              refine ⟨2904529363868014591586033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1936352909245343061057355 2904529363868014591586033)
              ·
                refine ⟨2178397022901010943689525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2904529363868014591586033 2178397022901010943689525)
                ·
                  refine ⟨204224720896969775970893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2178397022901010943689525 204224720896969775970893)
                  ·
                    rfl

theorem cell21_894884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 1, 2, 5].length) (baseStart_894884 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_894884 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_894884 prefixEnd_894884 := by exact prefixLift 894884
  have htrace : WordTrace (prefixWord ++ tailWord_894884) baseStart_894884 baseEnd_894884 := by
    simpa [prefixWord, tailWord_894884, baseEnd_894884] using wordTrace_append hprefix tailTrace_894884
  have hstable : (prefixWord ++ tailWord_894884).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_894884).length < 2 ^ (prefixWord ++ tailWord_894884).sum := by decide
  have hdescent : baseEnd_894884 < baseStart_894884 := by decide
  rcases family_descends (prefixWord ++ tailWord_894884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_894901 : List Nat := [1, 3, 3, 2, 1, 2, 1, 5, 3]
def baseStart_894901 : Nat := 118140960795 + 894901 * 2 ^ 59
def prefixEnd_894901 : Nat := 4983230072969 + 3 ^ 40 * 894901 * 2
def baseEnd_894901 : Nat := 204228600528581524187525

theorem tailTrace_894901 : CollatzResearch.WordTrace tailWord_894901 prefixEnd_894901 204228600528581524187525 := by
  unfold tailWord_894901
  simp only [CollatzResearch.WordTrace]
  refine ⟨32639720930933988767940557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21759813953955992511960371 32639720930933988767940557)
  ·
    refine ⟨12239895349100245787977709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32639720930933988767940557 12239895349100245787977709)
    ·
      refine ⟨4589960755912592170491641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12239895349100245787977709 4589960755912592170491641)
      ·
        refine ⟨3442470566934444127868731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4589960755912592170491641 3442470566934444127868731)
        ·
          refine ⟨5163705850401666191803097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3442470566934444127868731 5163705850401666191803097)
          ·
            refine ⟨3872779387801249643852323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5163705850401666191803097 3872779387801249643852323)
            ·
              refine ⟨5809169081701874465778485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3872779387801249643852323 5809169081701874465778485)
              ·
                refine ⟨544609601409550731166733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5809169081701874465778485 544609601409550731166733)
                ·
                  refine ⟨204228600528581524187525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 544609601409550731166733 204228600528581524187525)
                  ·
                    rfl

theorem cell21_894901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 5, 3].length) (baseStart_894901 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_894901 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_894901 prefixEnd_894901 := by exact prefixLift 894901
  have htrace : WordTrace (prefixWord ++ tailWord_894901) baseStart_894901 baseEnd_894901 := by
    simpa [prefixWord, tailWord_894901, baseEnd_894901] using wordTrace_append hprefix tailTrace_894901
  have hstable : (prefixWord ++ tailWord_894901).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_894901).length < 2 ^ (prefixWord ++ tailWord_894901).sum := by decide
  have hdescent : baseEnd_894901 < baseStart_894901 := by decide
  rcases family_descends (prefixWord ++ tailWord_894901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_894912 : List Nat := [2, 1, 1, 2, 3, 2, 10]
def baseStart_894912 : Nat := 118140960795 + 894912 * 2 ^ 59
def prefixEnd_894912 : Nat := 4983230072969 + 3 ^ 40 * 894912 * 2
def baseEnd_894912 : Nat := 22692345653160883278241

theorem tailTrace_894912 : CollatzResearch.WordTrace tailWord_894912 prefixEnd_894912 22692345653160883278241 := by
  unfold tailWord_894912
  simp only [CollatzResearch.WordTrace]
  refine ⟨16320061066947068823295495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21760081422596091764393993 16320061066947068823295495)
  ·
    refine ⟨24480091600420603234943243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16320061066947068823295495 24480091600420603234943243)
    ·
      refine ⟨36720137400630904852414865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24480091600420603234943243 36720137400630904852414865)
      ·
        refine ⟨27540103050473178639311149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36720137400630904852414865 27540103050473178639311149)
        ·
          refine ⟨10327538643927441989741681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27540103050473178639311149 10327538643927441989741681)
          ·
            refine ⟨7745653982945581492306261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10327538643927441989741681 7745653982945581492306261)
            ·
              refine ⟨22692345653160883278241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 7745653982945581492306261 22692345653160883278241)
              ·
                rfl

theorem cell21_894912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 10].length) (baseStart_894912 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_894912 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_894912 prefixEnd_894912 := by exact prefixLift 894912
  have htrace : WordTrace (prefixWord ++ tailWord_894912) baseStart_894912 baseEnd_894912 := by
    simpa [prefixWord, tailWord_894912, baseEnd_894912] using wordTrace_append hprefix tailTrace_894912
  have hstable : (prefixWord ++ tailWord_894912).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_894912).length < 2 ^ (prefixWord ++ tailWord_894912).sum := by decide
  have hdescent : baseEnd_894912 < baseStart_894912 := by decide
  rcases family_descends (prefixWord ++ tailWord_894912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_894932 : List Nat := [2, 4, 1, 2, 1, 1, 5, 1, 4]
def baseStart_894932 : Nat := 118140960795 + 894932 * 2 ^ 59
def prefixEnd_894932 : Nat := 4983230072969 + 3 ^ 40 * 894932 * 2
def baseEnd_894932 : Nat := 204235675150932359170795

theorem tailTrace_894932 : CollatzResearch.WordTrace tailWord_894932 prefixEnd_894932 204235675150932359170795 := by
  unfold tailWord_894932
  simp only [CollatzResearch.WordTrace]
  refine ⟨16320425796910840531159525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21760567729214454041546033 16320425796910840531159525)
  ·
    refine ⟨3060079836920782599592411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16320425796910840531159525 3060079836920782599592411)
    ·
      refine ⟨4590119755381173899388617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3060079836920782599592411 4590119755381173899388617)
      ·
        refine ⟨3442589816535880424541463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4590119755381173899388617 3442589816535880424541463)
        ·
          refine ⟨5163884724803820636812195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3442589816535880424541463 5163884724803820636812195)
          ·
            refine ⟨7745827087205730955218293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5163884724803820636812195 7745827087205730955218293)
            ·
              refine ⟨726171289425537277051715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7745827087205730955218293 726171289425537277051715)
              ·
                refine ⟨1089256934138305915577573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 726171289425537277051715 1089256934138305915577573)
                ·
                  refine ⟨204235675150932359170795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1089256934138305915577573 204235675150932359170795)
                  ·
                    rfl

theorem cell21_894932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 5, 1, 4].length) (baseStart_894932 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_894932 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_894932 prefixEnd_894932 := by exact prefixLift 894932
  have htrace : WordTrace (prefixWord ++ tailWord_894932) baseStart_894932 baseEnd_894932 := by
    simpa [prefixWord, tailWord_894932, baseEnd_894932] using wordTrace_append hprefix tailTrace_894932
  have hstable : (prefixWord ++ tailWord_894932).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_894932).length < 2 ^ (prefixWord ++ tailWord_894932).sum := by decide
  have hdescent : baseEnd_894932 < baseStart_894932 := by decide
  rcases family_descends (prefixWord ++ tailWord_894932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895005 : List Nat := [1, 4, 2, 2, 2, 1, 2, 7]
def baseStart_895005 : Nat := 118140960795 + 895005 * 2 ^ 59
def prefixEnd_895005 : Nat := 4983230072969 + 3 ^ 40 * 895005 * 2
def baseEnd_895005 : Nat := 68084111581833484817993

theorem tailTrace_895005 : CollatzResearch.WordTrace tailWord_895005 prefixEnd_895005 68084111581833484817993 := by
  unfold tailWord_895005
  simp only [CollatzResearch.WordTrace]
  refine ⟨32643514122557214529726469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21762342748371476353150979 32643514122557214529726469)
  ·
    refine ⟨6120658897979477724323713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32643514122557214529726469 6120658897979477724323713)
    ·
      refine ⟨4590494173484608293242785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6120658897979477724323713 4590494173484608293242785)
      ·
        refine ⟨3442870630113456219932089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4590494173484608293242785 3442870630113456219932089)
        ·
          refine ⟨2582152972585092164949067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3442870630113456219932089 2582152972585092164949067)
          ·
            refine ⟨3873229458877638247423601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2582152972585092164949067 3873229458877638247423601)
            ·
              refine ⟨2904922094158228685567701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3873229458877638247423601 2904922094158228685567701)
              ·
                refine ⟨68084111581833484817993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2904922094158228685567701 68084111581833484817993)
                ·
                  rfl

theorem cell21_895005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 2, 7].length) (baseStart_895005 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_895005 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_895005 prefixEnd_895005 := by exact prefixLift 895005
  have htrace : WordTrace (prefixWord ++ tailWord_895005) baseStart_895005 baseEnd_895005 := by
    simpa [prefixWord, tailWord_895005, baseEnd_895005] using wordTrace_append hprefix tailTrace_895005
  have hstable : (prefixWord ++ tailWord_895005).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895005).length < 2 ^ (prefixWord ++ tailWord_895005).sum := by decide
  have hdescent : baseEnd_895005 < baseStart_895005 := by decide
  rcases family_descends (prefixWord ++ tailWord_895005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895028 : List Nat := [2, 5, 1, 2, 2, 2, 2, 2, 3]
def baseStart_895028 : Nat := 118140960795 + 895028 * 2 ^ 59
def prefixEnd_895028 : Nat := 4983230072969 + 3 ^ 40 * 895028 * 2
def baseEnd_895028 : Nat := 204257583658857525570599

theorem tailTrace_895028 : CollatzResearch.WordTrace tailWord_895028 prefixEnd_895028 204257583658857525570599 := by
  unfold tailWord_895028
  simp only [CollatzResearch.WordTrace]
  refine ⟨16322176500736944728906869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21762902000982592971875825 16322176500736944728906869)
  ·
    refine ⟨1530204046944088568335019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16322176500736944728906869 1530204046944088568335019)
    ·
      refine ⟨2295306070416132852502529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1530204046944088568335019 2295306070416132852502529)
      ·
        refine ⟨1721479552812099639376897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2295306070416132852502529 1721479552812099639376897)
        ·
          refine ⟨1291109664609074729532673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1721479552812099639376897 1291109664609074729532673)
          ·
            refine ⟨968332248456806047149505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1291109664609074729532673 968332248456806047149505)
            ·
              refine ⟨726249186342604535362129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 968332248456806047149505 726249186342604535362129)
              ·
                refine ⟨544686889756953401521597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 726249186342604535362129 544686889756953401521597)
                ·
                  refine ⟨204257583658857525570599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 544686889756953401521597 204257583658857525570599)
                  ·
                    rfl

theorem cell21_895028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 2, 2, 3].length) (baseStart_895028 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_895028 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_895028 prefixEnd_895028 := by exact prefixLift 895028
  have htrace : WordTrace (prefixWord ++ tailWord_895028) baseStart_895028 baseEnd_895028 := by
    simpa [prefixWord, tailWord_895028, baseEnd_895028] using wordTrace_append hprefix tailTrace_895028
  have hstable : (prefixWord ++ tailWord_895028).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895028).length < 2 ^ (prefixWord ++ tailWord_895028).sum := by decide
  have hdescent : baseEnd_895028 < baseStart_895028 := by decide
  rcases family_descends (prefixWord ++ tailWord_895028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895095 : List Nat := [1, 1, 3, 1, 1, 5, 1, 3, 5]
def baseStart_895095 : Nat := 118140960795 + 895095 * 2 ^ 59
def prefixEnd_895095 : Nat := 4983230072969 + 3 ^ 40 * 895095 * 2
def baseEnd_895095 : Nat := 204272873971680297953795

theorem tailTrace_895095 : CollatzResearch.WordTrace tailWord_895095 prefixEnd_895095 204272873971680297953795 := by
  unfold tailWord_895095
  simp only [CollatzResearch.WordTrace]
  refine ⟨32646796692231159900502739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21764531128154106600335159 32646796692231159900502739)
  ·
    refine ⟨48970195038346739850754109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32646796692231159900502739 48970195038346739850754109)
    ·
      refine ⟨18363823139380027444032791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48970195038346739850754109 18363823139380027444032791)
      ·
        refine ⟨27545734709070041166049187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18363823139380027444032791 27545734709070041166049187)
        ·
          refine ⟨41318602063605061749073781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27545734709070041166049187 41318602063605061749073781)
          ·
            refine ⟨3873618943462974538975667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 41318602063605061749073781 3873618943462974538975667)
            ·
              refine ⟨5810428415194461808463501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3873618943462974538975667 5810428415194461808463501)
              ·
                refine ⟨2178910655697923178173813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5810428415194461808463501 2178910655697923178173813)
                ·
                  refine ⟨204272873971680297953795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2178910655697923178173813 204272873971680297953795)
                  ·
                    rfl

theorem cell21_895095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 3, 5].length) (baseStart_895095 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_895095 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_895095 prefixEnd_895095 := by exact prefixLift 895095
  have htrace : WordTrace (prefixWord ++ tailWord_895095) baseStart_895095 baseEnd_895095 := by
    simpa [prefixWord, tailWord_895095, baseEnd_895095] using wordTrace_append hprefix tailTrace_895095
  have hstable : (prefixWord ++ tailWord_895095).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895095).length < 2 ^ (prefixWord ++ tailWord_895095).sum := by decide
  have hdescent : baseEnd_895095 < baseStart_895095 := by decide
  rcases family_descends (prefixWord ++ tailWord_895095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895112 : List Nat := [2, 1, 3, 4, 1, 1, 2, 2, 5]
def baseStart_895112 : Nat := 118140960795 + 895112 * 2 ^ 59
def prefixEnd_895112 : Nat := 4983230072969 + 3 ^ 40 * 895112 * 2
def baseEnd_895112 : Nat := 204276753603292046170427

theorem tailTrace_895112 : CollatzResearch.WordTrace tailWord_895112 prefixEnd_895112 204276753603292046170427 := by
  unfold tailWord_895112
  simp only [CollatzResearch.WordTrace]
  refine ⟨16323708366584785901935795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21764944488779714535914393 16323708366584785901935795)
  ·
    refine ⟨24485562549877178852903693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16323708366584785901935795 24485562549877178852903693)
    ·
      refine ⟨9182085956203942069838885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24485562549877178852903693 9182085956203942069838885)
      ·
        refine ⟨1721641116788239138094791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9182085956203942069838885 1721641116788239138094791)
        ·
          refine ⟨2582461675182358707142187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1721641116788239138094791 2582461675182358707142187)
          ·
            refine ⟨3873692512773538060713281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2582461675182358707142187 3873692512773538060713281)
            ·
              refine ⟨2905269384580153545534961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3873692512773538060713281 2905269384580153545534961)
              ·
                refine ⟨2178952038435115159151221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2905269384580153545534961 2178952038435115159151221)
                ·
                  refine ⟨204276753603292046170427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2178952038435115159151221 204276753603292046170427)
                  ·
                    rfl

theorem cell21_895112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 2, 2, 5].length) (baseStart_895112 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_895112 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_895112 prefixEnd_895112 := by exact prefixLift 895112
  have htrace : WordTrace (prefixWord ++ tailWord_895112) baseStart_895112 baseEnd_895112 := by
    simpa [prefixWord, tailWord_895112, baseEnd_895112] using wordTrace_append hprefix tailTrace_895112
  have hstable : (prefixWord ++ tailWord_895112).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895112).length < 2 ^ (prefixWord ++ tailWord_895112).sum := by decide
  have hdescent : baseEnd_895112 < baseStart_895112 := by decide
  rcases family_descends (prefixWord ++ tailWord_895112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895146 : List Nat := [3, 1, 5, 1, 2, 2, 1, 1, 5]
def baseStart_895146 : Nat := 118140960795 + 895146 * 2 ^ 59
def prefixEnd_895146 : Nat := 4983230072969 + 3 ^ 40 * 895146 * 2
def baseEnd_895146 : Nat := 204284512866515542603691

theorem tailTrace_895146 : CollatzResearch.WordTrace tailWord_895146 prefixEnd_895146 204284512866515542603691 := by
  unfold tailWord_895146
  simp only [CollatzResearch.WordTrace]
  refine ⟨8162164203761598902652323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21765771210030930407072861 8162164203761598902652323)
  ·
    refine ⟨12243246305642398353978485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8162164203761598902652323 12243246305642398353978485)
    ·
      refine ⟨1147804341153974845685483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12243246305642398353978485 1147804341153974845685483)
      ·
        refine ⟨1721706511730962268528225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1147804341153974845685483 1721706511730962268528225)
        ·
          refine ⟨1291279883798221701396169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1721706511730962268528225 1291279883798221701396169)
          ·
            refine ⟨968459912848666276047127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1291279883798221701396169 968459912848666276047127)
            ·
              refine ⟨1452689869272999414070691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 968459912848666276047127 1452689869272999414070691)
              ·
                refine ⟨2179034803909499121106037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1452689869272999414070691 2179034803909499121106037)
                ·
                  refine ⟨204284512866515542603691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2179034803909499121106037 204284512866515542603691)
                  ·
                    rfl

theorem cell21_895146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 1, 1, 5].length) (baseStart_895146 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_895146 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_895146 prefixEnd_895146 := by exact prefixLift 895146
  have htrace : WordTrace (prefixWord ++ tailWord_895146) baseStart_895146 baseEnd_895146 := by
    simpa [prefixWord, tailWord_895146, baseEnd_895146] using wordTrace_append hprefix tailTrace_895146
  have hstable : (prefixWord ++ tailWord_895146).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895146).length < 2 ^ (prefixWord ++ tailWord_895146).sum := by decide
  have hdescent : baseEnd_895146 < baseStart_895146 := by decide
  rcases family_descends (prefixWord ++ tailWord_895146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895185 : List Nat := [1, 2, 2, 1, 2, 2, 2, 1, 8]
def baseStart_895185 : Nat := 118140960795 + 895185 * 2 ^ 59
def prefixEnd_895185 : Nat := 4983230072969 + 3 ^ 40 * 895185 * 2
def baseEnd_895185 : Nat := 204293413197860141453611

theorem tailTrace_895185 : CollatzResearch.WordTrace tailWord_895185 prefixEnd_895185 204293413197860141453611 := by
  unfold tailWord_895185
  simp only [CollatzResearch.WordTrace]
  refine ⟨32650079261905105271279009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21766719507936736847519339 32650079261905105271279009)
  ·
    refine ⟨24487559446428828953459257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32650079261905105271279009 24487559446428828953459257)
    ·
      refine ⟨18365669584821621715094443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24487559446428828953459257 18365669584821621715094443)
      ·
        refine ⟨27548504377232432572641665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18365669584821621715094443 27548504377232432572641665)
        ·
          refine ⟨20661378282924324429481249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27548504377232432572641665 20661378282924324429481249)
          ·
            refine ⟨15496033712193243322110937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20661378282924324429481249 15496033712193243322110937)
            ·
              refine ⟨11622025284144932491583203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15496033712193243322110937 11622025284144932491583203)
              ·
                refine ⟨17433037926217398737374805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11622025284144932491583203 17433037926217398737374805)
                ·
                  refine ⟨204293413197860141453611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 17433037926217398737374805 204293413197860141453611)
                  ·
                    rfl

theorem cell21_895185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 1, 8].length) (baseStart_895185 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_895185 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_895185 prefixEnd_895185 := by exact prefixLift 895185
  have htrace : WordTrace (prefixWord ++ tailWord_895185) baseStart_895185 baseEnd_895185 := by
    simpa [prefixWord, tailWord_895185, baseEnd_895185] using wordTrace_append hprefix tailTrace_895185
  have hstable : (prefixWord ++ tailWord_895185).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895185).length < 2 ^ (prefixWord ++ tailWord_895185).sum := by decide
  have hdescent : baseEnd_895185 < baseStart_895185 := by decide
  rcases family_descends (prefixWord ++ tailWord_895185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895205 : List Nat := [1, 3, 1, 4, 2, 2, 1, 4, 3]
def baseStart_895205 : Nat := 118140960795 + 895205 * 2 ^ 59
def prefixEnd_895205 : Nat := 4983230072969 + 3 ^ 40 * 895205 * 2
def baseEnd_895205 : Nat := 204297977470344551120237

theorem tailTrace_895205 : CollatzResearch.WordTrace tailWord_895205 prefixEnd_895205 204297977470344551120237 := by
  unfold tailWord_895205
  simp only [CollatzResearch.WordTrace]
  refine ⟨32650808721832648687007069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21767205814555099124671379 32650808721832648687007069)
  ·
    refine ⟨12244053270687243257627651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32650808721832648687007069 12244053270687243257627651)
    ·
      refine ⟨18366079906030864886441477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12244053270687243257627651 18366079906030864886441477)
      ·
        refine ⟨3443639982380787166207777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18366079906030864886441477 3443639982380787166207777)
        ·
          refine ⟨2582729986785590374655833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3443639982380787166207777 2582729986785590374655833)
          ·
            refine ⟨1937047490089192780991875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2582729986785590374655833 1937047490089192780991875)
            ·
              refine ⟨2905571235133789171487813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1937047490089192780991875 2905571235133789171487813)
              ·
                refine ⟨544794606587585469653965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2905571235133789171487813 544794606587585469653965)
                ·
                  refine ⟨204297977470344551120237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 544794606587585469653965 204297977470344551120237)
                  ·
                    rfl

theorem cell21_895205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 1, 4, 3].length) (baseStart_895205 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_895205 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_895205 prefixEnd_895205 := by exact prefixLift 895205
  have htrace : WordTrace (prefixWord ++ tailWord_895205) baseStart_895205 baseEnd_895205 := by
    simpa [prefixWord, tailWord_895205, baseEnd_895205] using wordTrace_append hprefix tailTrace_895205
  have hstable : (prefixWord ++ tailWord_895205).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895205).length < 2 ^ (prefixWord ++ tailWord_895205).sum := by decide
  have hdescent : baseEnd_895205 < baseStart_895205 := by decide
  rcases family_descends (prefixWord ++ tailWord_895205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895233 : List Nat := [1, 2, 4, 1, 1, 2, 5, 5]
def baseStart_895233 : Nat := 118140960795 + 895233 * 2 ^ 59
def prefixEnd_895233 : Nat := 4983230072969 + 3 ^ 40 * 895233 * 2
def baseEnd_895233 : Nat := 68101455817274241551171

theorem tailTrace_895233 : CollatzResearch.WordTrace tailWord_895233 prefixEnd_895233 68101455817274241551171 := by
  unfold tailWord_895233
  simp only [CollatzResearch.WordTrace]
  refine ⟨32651829965731209469026353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21767886643820806312684235 32651829965731209469026353)
  ·
    refine ⟨24488872474298407101769765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32651829965731209469026353 24488872474298407101769765)
    ·
      refine ⟨4591663588930951331581831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24488872474298407101769765 4591663588930951331581831)
      ·
        refine ⟨6887495383396426997372747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4591663588930951331581831 6887495383396426997372747)
        ·
          refine ⟨10331243075094640496059121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6887495383396426997372747 10331243075094640496059121)
          ·
            refine ⟨7748432306320980372044341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10331243075094640496059121 7748432306320980372044341)
            ·
              refine ⟨726415528717591909879157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7748432306320980372044341 726415528717591909879157)
              ·
                refine ⟨68101455817274241551171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 726415528717591909879157 68101455817274241551171)
                ·
                  rfl

theorem cell21_895233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 5, 5].length) (baseStart_895233 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_895233 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_895233 prefixEnd_895233 := by exact prefixLift 895233
  have htrace : WordTrace (prefixWord ++ tailWord_895233) baseStart_895233 baseEnd_895233 := by
    simpa [prefixWord, tailWord_895233, baseEnd_895233] using wordTrace_append hprefix tailTrace_895233
  have hstable : (prefixWord ++ tailWord_895233).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895233).length < 2 ^ (prefixWord ++ tailWord_895233).sum := by decide
  have hdescent : baseEnd_895233 < baseStart_895233 := by decide
  rcases family_descends (prefixWord ++ tailWord_895233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895264 : List Nat := [2, 1, 1, 5, 2, 2, 2, 1, 5]
def baseStart_895264 : Nat := 118140960795 + 895264 * 2 ^ 59
def prefixEnd_895264 : Nat := 4983230072969 + 3 ^ 40 * 895264 * 2
def baseEnd_895264 : Nat := 204311442074173559636783

theorem tailTrace_895264 : CollatzResearch.WordTrace tailWord_895264 prefixEnd_895264 204311442074173559636783 := by
  unfold tailWord_895264
  simp only [CollatzResearch.WordTrace]
  refine ⟨16326480314309450881702423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21768640419079267842269897 16326480314309450881702423)
  ·
    refine ⟨24489720471464176322553635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16326480314309450881702423 24489720471464176322553635)
    ·
      refine ⟨36734580707196264483830453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24489720471464176322553635 36734580707196264483830453)
      ·
        refine ⟨3443866941299649795359105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 36734580707196264483830453 3443866941299649795359105)
        ·
          refine ⟨2582900205974737346519329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3443866941299649795359105 2582900205974737346519329)
          ·
            refine ⟨1937175154481053009889497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2582900205974737346519329 1937175154481053009889497)
            ·
              refine ⟨1452881365860789757417123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1937175154481053009889497 1452881365860789757417123)
              ·
                refine ⟨2179322048791184636125685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1452881365860789757417123 2179322048791184636125685)
                ·
                  refine ⟨204311442074173559636783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2179322048791184636125685 204311442074173559636783)
                  ·
                    rfl

theorem cell21_895264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 2, 1, 5].length) (baseStart_895264 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_895264 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_895264 prefixEnd_895264 := by exact prefixLift 895264
  have htrace : WordTrace (prefixWord ++ tailWord_895264) baseStart_895264 baseEnd_895264 := by
    simpa [prefixWord, tailWord_895264, baseEnd_895264] using wordTrace_append hprefix tailTrace_895264
  have hstable : (prefixWord ++ tailWord_895264).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895264).length < 2 ^ (prefixWord ++ tailWord_895264).sum := by decide
  have hdescent : baseEnd_895264 < baseStart_895264 := by decide
  rcases family_descends (prefixWord ++ tailWord_895264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895292 : List Nat := [2, 2, 2, 2, 1, 2, 3, 7]
def baseStart_895292 : Nat := 118140960795 + 895292 * 2 ^ 59
def prefixEnd_895292 : Nat := 4983230072969 + 3 ^ 40 * 895292 * 2
def baseEnd_895292 : Nat := 68105944018550577723353

theorem tailTrace_895292 : CollatzResearch.WordTrace tailWord_895292 prefixEnd_895292 68105944018550577723353 := by
  unfold tailWord_895292
  simp only [CollatzResearch.WordTrace]
  refine ⟨16326990936258731272712065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21769321248344975030282753 16326990936258731272712065)
  ·
    refine ⟨12245243202194048454534049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16326990936258731272712065 12245243202194048454534049)
    ·
      refine ⟨9183932401645536340900537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12245243202194048454534049 9183932401645536340900537)
      ·
        refine ⟨6887949301234152255675403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9183932401645536340900537 6887949301234152255675403)
        ·
          refine ⟨10331923951851228383513105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6887949301234152255675403 10331923951851228383513105)
          ·
            refine ⟨7748942963888421287634829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10331923951851228383513105 7748942963888421287634829)
            ·
              refine ⟨2905853611458157982863061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7748942963888421287634829 2905853611458157982863061)
              ·
                refine ⟨68105944018550577723353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2905853611458157982863061 68105944018550577723353)
                ·
                  rfl

theorem cell21_895292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 3, 7].length) (baseStart_895292 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_895292 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_895292 prefixEnd_895292 := by exact prefixLift 895292
  have htrace : WordTrace (prefixWord ++ tailWord_895292) baseStart_895292 baseEnd_895292 := by
    simpa [prefixWord, tailWord_895292, baseEnd_895292] using wordTrace_append hprefix tailTrace_895292
  have hstable : (prefixWord ++ tailWord_895292).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895292).length < 2 ^ (prefixWord ++ tailWord_895292).sum := by decide
  have hdescent : baseEnd_895292 < baseStart_895292 := by decide
  rcases family_descends (prefixWord ++ tailWord_895292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895374 : List Nat := [4, 1, 1, 4, 1, 1, 4, 2, 3]
def baseStart_895374 : Nat := 118140960795 + 895374 * 2 ^ 59
def prefixEnd_895374 : Nat := 4983230072969 + 3 ^ 40 * 895374 * 2
def baseEnd_895374 : Nat := 204336545572837812803225

theorem tailTrace_895374 : CollatzResearch.WordTrace tailWord_895374 prefixEnd_895374 204336545572837812803225 := by
  unfold tailWord_895374
  simp only [CollatzResearch.WordTrace]
  refine ⟨4082121582277548818738647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21771315105480260366606117 4082121582277548818738647)
  ·
    refine ⟨6123182373416323228107971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4082121582277548818738647 6123182373416323228107971)
    ·
      refine ⟨9184773560124484842161957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6123182373416323228107971 9184773560124484842161957)
      ·
        refine ⟨1722145042523340907905367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9184773560124484842161957 1722145042523340907905367)
        ·
          refine ⟨2583217563785011361858051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1722145042523340907905367 2583217563785011361858051)
          ·
            refine ⟨3874826345677517042787077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2583217563785011361858051 3874826345677517042787077)
            ·
              refine ⟨726529939814534445522577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3874826345677517042787077 726529939814534445522577)
              ·
                refine ⟨544897454860900834141933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 726529939814534445522577 544897454860900834141933)
                ·
                  refine ⟨204336545572837812803225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 544897454860900834141933 204336545572837812803225)
                  ·
                    rfl

theorem cell21_895374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 4, 2, 3].length) (baseStart_895374 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_895374 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_895374 prefixEnd_895374 := by exact prefixLift 895374
  have htrace : WordTrace (prefixWord ++ tailWord_895374) baseStart_895374 baseEnd_895374 := by
    simpa [prefixWord, tailWord_895374, baseEnd_895374] using wordTrace_append hprefix tailTrace_895374
  have hstable : (prefixWord ++ tailWord_895374).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895374).length < 2 ^ (prefixWord ++ tailWord_895374).sum := by decide
  have hdescent : baseEnd_895374 < baseStart_895374 := by decide
  rcases family_descends (prefixWord ++ tailWord_895374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895399 : List Nat := [1, 1, 6, 1, 1, 2, 1, 1, 7]
def baseStart_895399 : Nat := 118140960795 + 895399 * 2 ^ 59
def prefixEnd_895399 : Nat := 4983230072969 + 3 ^ 40 * 895399 * 2
def baseEnd_895399 : Nat := 204342250913443324886507

theorem tailTrace_895399 : CollatzResearch.WordTrace tailWord_895399 prefixEnd_895399 204342250913443324886507 := by
  unfold tailWord_895399
  simp only [CollatzResearch.WordTrace]
  refine ⟨32657884483129819819569251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21771922988753213213046167 32657884483129819819569251)
  ·
    refine ⟨48986826724694729729353877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32657884483129819819569251 48986826724694729729353877)
    ·
      refine ⟨2296257502720065456063463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 48986826724694729729353877 2296257502720065456063463)
      ·
        refine ⟨3444386254080098184095195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2296257502720065456063463 3444386254080098184095195)
        ·
          refine ⟨5166579381120147276142793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3444386254080098184095195 5166579381120147276142793)
          ·
            refine ⟨3874934535840110457107095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5166579381120147276142793 3874934535840110457107095)
            ·
              refine ⟨5812401803760165685660643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3874934535840110457107095 5812401803760165685660643)
              ·
                refine ⟨8718602705640248528490965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5812401803760165685660643 8718602705640248528490965)
                ·
                  refine ⟨204342250913443324886507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8718602705640248528490965 204342250913443324886507)
                  ·
                    rfl

theorem cell21_895399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 1, 7].length) (baseStart_895399 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_895399 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_895399 prefixEnd_895399 := by exact prefixLift 895399
  have htrace : WordTrace (prefixWord ++ tailWord_895399) baseStart_895399 baseEnd_895399 := by
    simpa [prefixWord, tailWord_895399, baseEnd_895399] using wordTrace_append hprefix tailTrace_895399
  have hstable : (prefixWord ++ tailWord_895399).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895399).length < 2 ^ (prefixWord ++ tailWord_895399).sum := by decide
  have hdescent : baseEnd_895399 < baseStart_895399 := by decide
  rcases family_descends (prefixWord ++ tailWord_895399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895461 : List Nat := [1, 3, 1, 5, 2, 1, 1, 7]
def baseStart_895461 : Nat := 118140960795 + 895461 * 2 ^ 59
def prefixEnd_895461 : Nat := 4983230072969 + 3 ^ 40 * 895461 * 2
def baseEnd_895461 : Nat := 68118800052714998284349

theorem tailTrace_895461 : CollatzResearch.WordTrace tailWord_895461 prefixEnd_895461 68118800052714998284349 := by
  unfold tailWord_895461
  simp only [CollatzResearch.WordTrace]
  refine ⟨32660145808905204408326237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21773430539270136272217491 32660145808905204408326237)
  ·
    refine ⟨12247554678339451653122339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32660145808905204408326237 12247554678339451653122339)
    ·
      refine ⟨18371332017509177479683509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12247554678339451653122339 18371332017509177479683509)
      ·
        refine ⟨1722312376641485388720329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 18371332017509177479683509 1722312376641485388720329)
        ·
          refine ⟨1291734282481114041540247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1722312376641485388720329 1291734282481114041540247)
          ·
            refine ⟨1937601423721671062310371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1291734282481114041540247 1937601423721671062310371)
            ·
              refine ⟨2906402135582506593465557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1937601423721671062310371 2906402135582506593465557)
              ·
                refine ⟨68118800052714998284349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2906402135582506593465557 68118800052714998284349)
                ·
                  rfl

theorem cell21_895461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 1, 7].length) (baseStart_895461 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_895461 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_895461 prefixEnd_895461 := by exact prefixLift 895461
  have htrace : WordTrace (prefixWord ++ tailWord_895461) baseStart_895461 baseEnd_895461 := by
    simpa [prefixWord, tailWord_895461, baseEnd_895461] using wordTrace_append hprefix tailTrace_895461
  have hstable : (prefixWord ++ tailWord_895461).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895461).length < 2 ^ (prefixWord ++ tailWord_895461).sum := by decide
  have hdescent : baseEnd_895461 < baseStart_895461 := by decide
  rcases family_descends (prefixWord ++ tailWord_895461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895492 : List Nat := [2, 3, 2, 3, 1, 1, 3, 1, 5]
def baseStart_895492 : Nat := 118140960795 + 895492 * 2 ^ 59
def prefixEnd_895492 : Nat := 4983230072969 + 3 ^ 40 * 895492 * 2
def baseEnd_895492 : Nat := 204363474780495829836317

theorem tailTrace_895492 : CollatzResearch.WordTrace tailWord_895492 prefixEnd_895492 204363474780495829836317 := by
  unfold tailWord_895492
  simp only [CollatzResearch.WordTrace]
  refine ⟨16330638235896448351352365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21774184314528597801803153 16330638235896448351352365)
  ·
    refine ⟨6123989338461168131757137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16330638235896448351352365 6123989338461168131757137)
    ·
      refine ⟨4592992003845876098817853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6123989338461168131757137 4592992003845876098817853)
      ·
        refine ⟨1722372001442203537056695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4592992003845876098817853 1722372001442203537056695)
        ·
          refine ⟨2583558002163305305585043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1722372001442203537056695 2583558002163305305585043)
          ·
            refine ⟨3875337003244957958377565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2583558002163305305585043 3875337003244957958377565)
            ·
              refine ⟨1453251376216859234391587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3875337003244957958377565 1453251376216859234391587)
              ·
                refine ⟨2179877064325288851587381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1453251376216859234391587 2179877064325288851587381)
                ·
                  refine ⟨204363474780495829836317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2179877064325288851587381 204363474780495829836317)
                  ·
                    rfl

theorem cell21_895492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 3, 1, 5].length) (baseStart_895492 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_895492 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_895492 prefixEnd_895492 := by exact prefixLift 895492
  have htrace : WordTrace (prefixWord ++ tailWord_895492) baseStart_895492 baseEnd_895492 := by
    simpa [prefixWord, tailWord_895492, baseEnd_895492] using wordTrace_append hprefix tailTrace_895492
  have hstable : (prefixWord ++ tailWord_895492).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895492).length < 2 ^ (prefixWord ++ tailWord_895492).sum := by decide
  have hdescent : baseEnd_895492 < baseStart_895492 := by decide
  rcases family_descends (prefixWord ++ tailWord_895492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895503 : List Nat := [1, 1, 2, 1, 1, 1, 2, 12]
def baseStart_895503 : Nat := 118140960795 + 895503 * 2 ^ 59
def prefixEnd_895503 : Nat := 4983230072969 + 3 ^ 40 * 895503 * 2
def baseEnd_895503 : Nat := 68121995043454085050987

theorem tailTrace_895503 : CollatzResearch.WordTrace tailWord_895503 prefixEnd_895503 68121995043454085050987 := by
  unfold tailWord_895503
  simp only [CollatzResearch.WordTrace]
  refine ⟨32661677674753045581355163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21774451783168697054236775 32661677674753045581355163)
  ·
    refine ⟨48992516512129568372032745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32661677674753045581355163 48992516512129568372032745)
    ·
      refine ⟨36744387384097176279024559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48992516512129568372032745 36744387384097176279024559)
      ·
        refine ⟨55116581076145764418536839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36744387384097176279024559 55116581076145764418536839)
        ·
          refine ⟨82674871614218646627805259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55116581076145764418536839 82674871614218646627805259)
          ·
            refine ⟨124012307421327969941707889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82674871614218646627805259 124012307421327969941707889)
            ·
              refine ⟨93009230565995977456280917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124012307421327969941707889 93009230565995977456280917)
              ·
                refine ⟨68121995043454085050987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 93009230565995977456280917 68121995043454085050987)
                ·
                  rfl

theorem cell21_895503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 12].length) (baseStart_895503 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_895503 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_895503 prefixEnd_895503 := by exact prefixLift 895503
  have htrace : WordTrace (prefixWord ++ tailWord_895503) baseStart_895503 baseEnd_895503 := by
    simpa [prefixWord, tailWord_895503, baseEnd_895503] using wordTrace_append hprefix tailTrace_895503
  have hstable : (prefixWord ++ tailWord_895503).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895503).length < 2 ^ (prefixWord ++ tailWord_895503).sum := by decide
  have hdescent : baseEnd_895503 < baseStart_895503 := by decide
  rcases family_descends (prefixWord ++ tailWord_895503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895734 : List Nat := [5, 1, 1, 1, 1, 2, 1, 5, 4]
def baseStart_895734 : Nat := 118140960795 + 895734 * 2 ^ 59
def prefixEnd_895734 : Nat := 4983230072969 + 3 ^ 40 * 895734 * 2
def baseEnd_895734 : Nat := 204418702477557186802489

theorem tailTrace_895734 : CollatzResearch.WordTrace tailWord_895734 prefixEnd_895734 204418702477557186802489 := by
  unfold tailWord_895734
  simp only [CollatzResearch.WordTrace]
  refine ⟨2041881433557260752063391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21780068624610781355342837 2041881433557260752063391)
  ·
    refine ⟨3062822150335891128095087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2041881433557260752063391 3062822150335891128095087)
    ·
      refine ⟨4594233225503836692142631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3062822150335891128095087 4594233225503836692142631)
      ·
        refine ⟨6891349838255755038213947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4594233225503836692142631 6891349838255755038213947)
        ·
          refine ⟨10337024757383632557320921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6891349838255755038213947 10337024757383632557320921)
          ·
            refine ⟨7752768568037724417990691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10337024757383632557320921 7752768568037724417990691)
            ·
              refine ⟨11629152852056586626986037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7752768568037724417990691 11629152852056586626986037)
              ·
                refine ⟨1090233079880304996279941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11629152852056586626986037 1090233079880304996279941)
                ·
                  refine ⟨204418702477557186802489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1090233079880304996279941 204418702477557186802489)
                  ·
                    rfl

theorem cell21_895734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 5, 4].length) (baseStart_895734 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_895734 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_895734 prefixEnd_895734 := by exact prefixLift 895734
  have htrace : WordTrace (prefixWord ++ tailWord_895734) baseStart_895734 baseEnd_895734 := by
    simpa [prefixWord, tailWord_895734, baseEnd_895734] using wordTrace_append hprefix tailTrace_895734
  have hstable : (prefixWord ++ tailWord_895734).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895734).length < 2 ^ (prefixWord ++ tailWord_895734).sum := by decide
  have hdescent : baseEnd_895734 < baseStart_895734 := by decide
  rcases family_descends (prefixWord ++ tailWord_895734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895976 : List Nat := [2, 1, 4, 1, 1, 1, 6, 5]
def baseStart_895976 : Nat := 118140960795 + 895976 * 2 ^ 59
def prefixEnd_895976 : Nat := 4983230072969 + 3 ^ 40 * 895976 * 2
def baseEnd_895976 : Nat := 68157976724872847922887

theorem tailTrace_895976 : CollatzResearch.WordTrace tailWord_895976 prefixEnd_895976 68157976724872847922887 := by
  unfold tailWord_895976
  simp only [CollatzResearch.WordTrace]
  refine ⟨16339464701019723681661891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21785952934692964908882521 16339464701019723681661891)
  ·
    refine ⟨24509197051529585522492837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16339464701019723681661891 24509197051529585522492837)
    ·
      refine ⟨4595474447161797285467407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24509197051529585522492837 4595474447161797285467407)
      ·
        refine ⟨6893211670742695928201111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4595474447161797285467407 6893211670742695928201111)
        ·
          refine ⟨10339817506114043892301667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6893211670742695928201111 10339817506114043892301667)
          ·
            refine ⟨15509726259171065838452501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10339817506114043892301667 15509726259171065838452501)
            ·
              refine ⟨727018418398643711177461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 15509726259171065838452501 727018418398643711177461)
              ·
                refine ⟨68157976724872847922887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 727018418398643711177461 68157976724872847922887)
                ·
                  rfl

theorem cell21_895976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 6, 5].length) (baseStart_895976 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_895976 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_895976 prefixEnd_895976 := by exact prefixLift 895976
  have htrace : WordTrace (prefixWord ++ tailWord_895976) baseStart_895976 baseEnd_895976 := by
    simpa [prefixWord, tailWord_895976, baseEnd_895976] using wordTrace_append hprefix tailTrace_895976
  have hstable : (prefixWord ++ tailWord_895976).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895976).length < 2 ^ (prefixWord ++ tailWord_895976).sum := by decide
  have hdescent : baseEnd_895976 < baseStart_895976 := by decide
  rcases family_descends (prefixWord ++ tailWord_895976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895982 : List Nat := [4, 1, 2, 1, 5, 1, 1, 3, 3]
def baseStart_895982 : Nat := 118140960795 + 895982 * 2 ^ 59
def prefixEnd_895982 : Nat := 4983230072969 + 3 ^ 40 * 895982 * 2
def baseEnd_895982 : Nat := 204475299456363866668649

theorem tailTrace_895982 : CollatzResearch.WordTrace tailWord_895982 prefixEnd_895982 204475299456363866668649 := by
  unfold tailWord_895982
  simp only [CollatzResearch.WordTrace]
  refine ⟨4084893530002213798505275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21786098826678473592028133 4084893530002213798505275)
  ·
    refine ⟨6127340295003320697757913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4084893530002213798505275 6127340295003320697757913)
    ·
      refine ⟨4595505221252490523318435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6127340295003320697757913 4595505221252490523318435)
      ·
        refine ⟨6893257831878735784977653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4595505221252490523318435 6893257831878735784977653)
        ·
          refine ⟨646242921738631479841655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6893257831878735784977653 646242921738631479841655)
          ·
            refine ⟨969364382607947219762483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 646242921738631479841655 969364382607947219762483)
            ·
              refine ⟨1454046573911920829643725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 969364382607947219762483 1454046573911920829643725)
              ·
                refine ⟨545267465216970311116397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1454046573911920829643725 545267465216970311116397)
                ·
                  refine ⟨204475299456363866668649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 545267465216970311116397 204475299456363866668649)
                  ·
                    rfl

theorem cell21_895982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 1, 3, 3].length) (baseStart_895982 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_895982 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_895982 prefixEnd_895982 := by exact prefixLift 895982
  have htrace : WordTrace (prefixWord ++ tailWord_895982) baseStart_895982 baseEnd_895982 := by
    simpa [prefixWord, tailWord_895982, baseEnd_895982] using wordTrace_append hprefix tailTrace_895982
  have hstable : (prefixWord ++ tailWord_895982).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895982).length < 2 ^ (prefixWord ++ tailWord_895982).sum := by decide
  have hdescent : baseEnd_895982 < baseStart_895982 := by decide
  rcases family_descends (prefixWord ++ tailWord_895982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_896035 : List Nat := [1, 1, 1, 4, 3, 2, 2, 7]
def baseStart_896035 : Nat := 118140960795 + 896035 * 2 ^ 59
def prefixEnd_896035 : Nat := 4983230072969 + 3 ^ 40 * 896035 * 2
def baseEnd_896035 : Nat := 68162464926149184095069

theorem tailTrace_896035 : CollatzResearch.WordTrace tailWord_896035 prefixEnd_896035 68162464926149184095069 := by
  unfold tailWord_896035
  simp only [CollatzResearch.WordTrace]
  refine ⟨32681081308825700439721559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21787387539217133626481039 32681081308825700439721559)
  ·
    refine ⟨49021621963238550659582339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32681081308825700439721559 49021621963238550659582339)
    ·
      refine ⟨73532432944857825989373509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49021621963238550659582339 73532432944857825989373509)
      ·
        refine ⟨13787331177160842373007533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 73532432944857825989373509 13787331177160842373007533)
        ·
          refine ⟨5170249191435315889877825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13787331177160842373007533 5170249191435315889877825)
          ·
            refine ⟨3877686893576486917408369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5170249191435315889877825 3877686893576486917408369)
            ·
              refine ⟨2908265170182365188056277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3877686893576486917408369 2908265170182365188056277)
              ·
                refine ⟨68162464926149184095069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2908265170182365188056277 68162464926149184095069)
                ·
                  rfl

theorem cell21_896035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 2, 7].length) (baseStart_896035 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_896035 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_896035 prefixEnd_896035 := by exact prefixLift 896035
  have htrace : WordTrace (prefixWord ++ tailWord_896035) baseStart_896035 baseEnd_896035 := by
    simpa [prefixWord, tailWord_896035, baseEnd_896035] using wordTrace_append hprefix tailTrace_896035
  have hstable : (prefixWord ++ tailWord_896035).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_896035).length < 2 ^ (prefixWord ++ tailWord_896035).sum := by decide
  have hdescent : baseEnd_896035 < baseStart_896035 := by decide
  rcases family_descends (prefixWord ++ tailWord_896035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_896052 : List Nat := [2, 5, 1, 2, 1, 10]
def baseStart_896052 : Nat := 118140960795 + 896052 * 2 ^ 59
def prefixEnd_896052 : Nat := 4983230072969 + 3 ^ 40 * 896052 * 2
def baseEnd_896052 : Nat := 7573750904076270388957

theorem tailTrace_896052 : CollatzResearch.WordTrace tailWord_896052 prefixEnd_896052 7573750904076270388957 := by
  unfold tailWord_896052
  simp only [CollatzResearch.WordTrace]
  refine ⟨16340850674882056171545205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21787800899842741562060273 16340850674882056171545205)
  ·
    refine ⟨1531954750770192766082363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16340850674882056171545205 1531954750770192766082363)
    ·
      refine ⟨2297932126155289149123545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1531954750770192766082363 2297932126155289149123545)
      ·
        refine ⟨1723449094616466861842659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2297932126155289149123545 1723449094616466861842659)
        ·
          refine ⟨2585173641924700292763989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1723449094616466861842659 2585173641924700292763989)
          ·
            refine ⟨7573750904076270388957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2585173641924700292763989 7573750904076270388957)
            ·
              rfl

theorem cell21_896052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 10].length) (baseStart_896052 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_896052 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_896052 prefixEnd_896052 := by exact prefixLift 896052
  have htrace : WordTrace (prefixWord ++ tailWord_896052) baseStart_896052 baseEnd_896052 := by
    simpa [prefixWord, tailWord_896052, baseEnd_896052] using wordTrace_append hprefix tailTrace_896052
  have hstable : (prefixWord ++ tailWord_896052).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_896052).length < 2 ^ (prefixWord ++ tailWord_896052).sum := by decide
  have hdescent : baseEnd_896052 < baseStart_896052 := by decide
  rcases family_descends (prefixWord ++ tailWord_896052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_896182 : List Nat := [5, 1, 3, 2, 2, 1, 2, 1, 4]
def baseStart_896182 : Nat := 118140960795 + 896182 * 2 ^ 59
def prefixEnd_896182 : Nat := 4983230072969 + 3 ^ 40 * 896182 * 2
def baseEnd_896182 : Nat := 204520942181207963334907

theorem tailTrace_896182 : CollatzResearch.WordTrace tailWord_896182 prefixEnd_896182 204520942181207963334907 := by
  unfold tailWord_896182
  simp only [CollatzResearch.WordTrace]
  refine ⟨2042902677455821534082675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21790961892862096363548533 2042902677455821534082675)
  ·
    refine ⟨3064354016183732301124013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2042902677455821534082675 3064354016183732301124013)
    ·
      refine ⟨1149132756068899612921505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3064354016183732301124013 1149132756068899612921505)
      ·
        refine ⟨861849567051674709691129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1149132756068899612921505 861849567051674709691129)
        ·
          refine ⟨646387175288756032268347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 861849567051674709691129 646387175288756032268347)
          ·
            refine ⟨969580762933134048402521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 646387175288756032268347 969580762933134048402521)
            ·
              refine ⟨727185572199850536301891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 969580762933134048402521 727185572199850536301891)
              ·
                refine ⟨1090778358299775804452837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 727185572199850536301891 1090778358299775804452837)
                ·
                  refine ⟨204520942181207963334907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1090778358299775804452837 204520942181207963334907)
                  ·
                    rfl

theorem cell21_896182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 2, 1, 4].length) (baseStart_896182 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_896182 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_896182 prefixEnd_896182 := by exact prefixLift 896182
  have htrace : WordTrace (prefixWord ++ tailWord_896182) baseStart_896182 baseEnd_896182 := by
    simpa [prefixWord, tailWord_896182, baseEnd_896182] using wordTrace_append hprefix tailTrace_896182
  have hstable : (prefixWord ++ tailWord_896182).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_896182).length < 2 ^ (prefixWord ++ tailWord_896182).sum := by decide
  have hdescent : baseEnd_896182 < baseStart_896182 := by decide
  rcases family_descends (prefixWord ++ tailWord_896182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_896190 : List Nat := [4, 2, 1, 1, 3, 2, 1, 3, 4]
def baseStart_896190 : Nat := 118140960795 + 896190 * 2 ^ 59
def prefixEnd_896190 : Nat := 4983230072969 + 3 ^ 40 * 896190 * 2
def baseEnd_896190 : Nat := 204522767890201727201557

theorem tailTrace_896190 : CollatzResearch.WordTrace tailWord_896190 prefixEnd_896190 204522767890201727201557 := by
  unfold tailWord_896190
  simp only [CollatzResearch.WordTrace]
  refine ⟨4085841827908020238951753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21791156415509441274409349 4085841827908020238951753)
  ·
    refine ⟨3064381370931015179213815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4085841827908020238951753 3064381370931015179213815)
    ·
      refine ⟨4596572056396522768820723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3064381370931015179213815 4596572056396522768820723)
      ·
        refine ⟨6894858084594784153231085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4596572056396522768820723 6894858084594784153231085)
        ·
          refine ⟨2585571781723044057461657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6894858084594784153231085 2585571781723044057461657)
          ·
            refine ⟨1939178836292283043096243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2585571781723044057461657 1939178836292283043096243)
            ·
              refine ⟨2908768254438424564644365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1939178836292283043096243 2908768254438424564644365)
              ·
                refine ⟨1090788095414409211741637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2908768254438424564644365 1090788095414409211741637)
                ·
                  refine ⟨204522767890201727201557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1090788095414409211741637 204522767890201727201557)
                  ·
                    rfl

theorem cell21_896190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 1, 3, 4].length) (baseStart_896190 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_896190 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_896190 prefixEnd_896190 := by exact prefixLift 896190
  have htrace : WordTrace (prefixWord ++ tailWord_896190) baseStart_896190 baseEnd_896190 := by
    simpa [prefixWord, tailWord_896190, baseEnd_896190] using wordTrace_append hprefix tailTrace_896190
  have hstable : (prefixWord ++ tailWord_896190).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_896190).length < 2 ^ (prefixWord ++ tailWord_896190).sum := by decide
  have hdescent : baseEnd_896190 < baseStart_896190 := by decide
  rcases family_descends (prefixWord ++ tailWord_896190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_896235 : List Nat := [1, 1, 1, 1, 2, 7, 1, 4, 3]
def baseStart_896235 : Nat := 118140960795 + 896235 * 2 ^ 59
def prefixEnd_896235 : Nat := 4983230072969 + 3 ^ 40 * 896235 * 2
def baseEnd_896235 : Nat := 204533037503291648951465

theorem tailTrace_896235 : CollatzResearch.WordTrace tailWord_896235 prefixEnd_896235 204533037503291648951465 := by
  unfold tailWord_896235
  simp only [CollatzResearch.WordTrace]
  refine ⟨32688375908101134597002159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21792250605400756398001439 32688375908101134597002159)
  ·
    refine ⟨49032563862151701895503239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32688375908101134597002159 49032563862151701895503239)
    ·
      refine ⟨73548845793227552843254859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49032563862151701895503239 73548845793227552843254859)
      ·
        refine ⟨110323268689841329264882289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73548845793227552843254859 110323268689841329264882289)
        ·
          refine ⟨82742451517380996948661717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110323268689841329264882289 82742451517380996948661717)
          ·
            refine ⟨1939276207438617115984259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 82742451517380996948661717 1939276207438617115984259)
            ·
              refine ⟨2908914311157925673976389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1939276207438617115984259 2908914311157925673976389)
              ·
                refine ⟨545421433342111063870573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2908914311157925673976389 545421433342111063870573)
                ·
                  refine ⟨204533037503291648951465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 545421433342111063870573 204533037503291648951465)
                  ·
                    rfl

theorem cell21_896235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 1, 4, 3].length) (baseStart_896235 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_896235 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_896235 prefixEnd_896235 := by exact prefixLift 896235
  have htrace : WordTrace (prefixWord ++ tailWord_896235) baseStart_896235 baseEnd_896235 := by
    simpa [prefixWord, tailWord_896235, baseEnd_896235] using wordTrace_append hprefix tailTrace_896235
  have hstable : (prefixWord ++ tailWord_896235).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_896235).length < 2 ^ (prefixWord ++ tailWord_896235).sum := by decide
  have hdescent : baseEnd_896235 < baseStart_896235 := by decide
  rcases family_descends (prefixWord ++ tailWord_896235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_896277 : List Nat := [1, 3, 2, 1, 2, 1, 1, 1, 9]
def baseStart_896277 : Nat := 118140960795 + 896277 * 2 ^ 59
def prefixEnd_896277 : Nat := 4983230072969 + 3 ^ 40 * 896277 * 2
def baseEnd_896277 : Nat := 204542622475508909251379

theorem tailTrace_896277 : CollatzResearch.WordTrace tailWord_896277 prefixEnd_896277 204542622475508909251379 := by
  unfold tailWord_896277
  simp only [CollatzResearch.WordTrace]
  refine ⟨32689907773948975770031085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21793271849299317180020723 32689907773948975770031085)
  ·
    refine ⟨12258715415230865913761657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32689907773948975770031085 12258715415230865913761657)
    ·
      refine ⟨9194036561423149435321243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12258715415230865913761657 9194036561423149435321243)
      ·
        refine ⟨13791054842134724152981865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9194036561423149435321243 13791054842134724152981865)
        ·
          refine ⟨10343291131601043114736399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13791054842134724152981865 10343291131601043114736399)
          ·
            refine ⟨15514936697401564672104599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10343291131601043114736399 15514936697401564672104599)
            ·
              refine ⟨23272405046102347008156899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15514936697401564672104599 23272405046102347008156899)
              ·
                refine ⟨34908607569153520512235349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23272405046102347008156899 34908607569153520512235349)
                ·
                  refine ⟨204542622475508909251379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 34908607569153520512235349 204542622475508909251379)
                  ·
                    rfl

theorem cell21_896277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 1, 9].length) (baseStart_896277 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_896277 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_896277 prefixEnd_896277 := by exact prefixLift 896277
  have htrace : WordTrace (prefixWord ++ tailWord_896277) baseStart_896277 baseEnd_896277 := by
    simpa [prefixWord, tailWord_896277, baseEnd_896277] using wordTrace_append hprefix tailTrace_896277
  have hstable : (prefixWord ++ tailWord_896277).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_896277).length < 2 ^ (prefixWord ++ tailWord_896277).sum := by decide
  have hdescent : baseEnd_896277 < baseStart_896277 := by decide
  rcases family_descends (prefixWord ++ tailWord_896277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_896359 : List Nat := [1, 1, 5, 1, 4, 2, 2, 1, 4]
def baseStart_896359 : Nat := 118140960795 + 896359 * 2 ^ 59
def prefixEnd_896359 : Nat := 4983230072969 + 3 ^ 40 * 896359 * 2
def baseEnd_896359 : Nat := 204561335992694988884545

theorem tailTrace_896359 : CollatzResearch.WordTrace tailWord_896359 prefixEnd_896359 204561335992694988884545 := by
  unfold tailWord_896359
  simp only [CollatzResearch.WordTrace]
  refine ⟨32692898559651903774516131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21795265706434602516344087 32692898559651903774516131)
  ·
    refine ⟨49039347839477855661774197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32692898559651903774516131 49039347839477855661774197)
    ·
      refine ⟨4597438859951048968291331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 49039347839477855661774197 4597438859951048968291331)
      ·
        refine ⟨6896158289926573452436997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4597438859951048968291331 6896158289926573452436997)
        ·
          refine ⟨1293029679361232522331937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6896158289926573452436997 1293029679361232522331937)
          ·
            refine ⟨969772259520924391748953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1293029679361232522331937 969772259520924391748953)
            ·
              refine ⟨727329194640693293811715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 969772259520924391748953 727329194640693293811715)
              ·
                refine ⟨1090993791961039940717573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 727329194640693293811715 1090993791961039940717573)
                ·
                  refine ⟨204561335992694988884545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1090993791961039940717573 204561335992694988884545)
                  ·
                    rfl

theorem cell21_896359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 2, 1, 4].length) (baseStart_896359 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_896359 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_896359 prefixEnd_896359 := by exact prefixLift 896359
  have htrace : WordTrace (prefixWord ++ tailWord_896359) baseStart_896359 baseEnd_896359 := by
    simpa [prefixWord, tailWord_896359, baseEnd_896359] using wordTrace_append hprefix tailTrace_896359
  have hstable : (prefixWord ++ tailWord_896359).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_896359).length < 2 ^ (prefixWord ++ tailWord_896359).sum := by decide
  have hdescent : baseEnd_896359 < baseStart_896359 := by decide
  rcases family_descends (prefixWord ++ tailWord_896359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_896404 : List Nat := [2, 4, 2, 1, 2, 2, 1, 4, 3]
def baseStart_896404 : Nat := 118140960795 + 896404 * 2 ^ 59
def prefixEnd_896404 : Nat := 4983230072969 + 3 ^ 40 * 896404 * 2
def baseEnd_896404 : Nat := 204571605605784910634453

theorem tailTrace_896404 : CollatzResearch.WordTrace tailWord_896404 prefixEnd_896404 204571605605784910634453 := by
  unfold tailWord_896404
  simp only [CollatzResearch.WordTrace]
  refine ⟨16347269922244438229952133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21796359896325917639936177 16347269922244438229952133)
  ·
    refine ⟨3065113110420832168116025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16347269922244438229952133 3065113110420832168116025)
    ·
      refine ⟨2298834832815624126087019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3065113110420832168116025 2298834832815624126087019)
      ·
        refine ⟨3448252249223436189130529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2298834832815624126087019 3448252249223436189130529)
        ·
          refine ⟨2586189186917577141847897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3448252249223436189130529 2586189186917577141847897)
          ·
            refine ⟨1939641890188182856385923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2586189186917577141847897 1939641890188182856385923)
            ·
              refine ⟨2909462835282274284578885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1939641890188182856385923 2909462835282274284578885)
              ·
                refine ⟨545524281615426428358541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2909462835282274284578885 545524281615426428358541)
                ·
                  refine ⟨204571605605784910634453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 545524281615426428358541 204571605605784910634453)
                  ·
                    rfl

theorem cell21_896404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 1, 4, 3].length) (baseStart_896404 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_896404 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_896404 prefixEnd_896404 := by exact prefixLift 896404
  have htrace : WordTrace (prefixWord ++ tailWord_896404) baseStart_896404 baseEnd_896404 := by
    simpa [prefixWord, tailWord_896404, baseEnd_896404] using wordTrace_append hprefix tailTrace_896404
  have hstable : (prefixWord ++ tailWord_896404).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_896404).length < 2 ^ (prefixWord ++ tailWord_896404).sum := by decide
  have hdescent : baseEnd_896404 < baseStart_896404 := by decide
  rcases family_descends (prefixWord ++ tailWord_896404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_896415 : List Nat := [1, 1, 2, 5, 1, 2, 3, 6]
def baseStart_896415 : Nat := 118140960795 + 896415 * 2 ^ 59
def prefixEnd_896415 : Nat := 4983230072969 + 3 ^ 40 * 896415 * 2
def baseEnd_896415 : Nat := 68191371985217111983699

theorem tailTrace_896415 : CollatzResearch.WordTrace tailWord_896415 prefixEnd_896415 68191371985217111983699 := by
  unfold tailWord_896415
  simp only [CollatzResearch.WordTrace]
  refine ⟨32694941047449025338554699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21796627364966016892369799 32694941047449025338554699)
  ·
    refine ⟨49042411571173538007832049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32694941047449025338554699 49042411571173538007832049)
    ·
      refine ⟨36781808678380153505874037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49042411571173538007832049 36781808678380153505874037)
      ·
        refine ⟨3448294563598139391175691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 36781808678380153505874037 3448294563598139391175691)
        ·
          refine ⟨5172441845397209086763537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3448294563598139391175691 5172441845397209086763537)
          ·
            refine ⟨3879331384047906815072653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5172441845397209086763537 3879331384047906815072653)
            ·
              refine ⟨1454749269017965055652245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3879331384047906815072653 1454749269017965055652245)
              ·
                refine ⟨68191371985217111983699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1454749269017965055652245 68191371985217111983699)
                ·
                  rfl

theorem cell21_896415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 3, 6].length) (baseStart_896415 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_896415 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_896415 prefixEnd_896415 := by exact prefixLift 896415
  have htrace : WordTrace (prefixWord ++ tailWord_896415) baseStart_896415 baseEnd_896415 := by
    simpa [prefixWord, tailWord_896415, baseEnd_896415] using wordTrace_append hprefix tailTrace_896415
  have hstable : (prefixWord ++ tailWord_896415).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_896415).length < 2 ^ (prefixWord ++ tailWord_896415).sum := by decide
  have hdescent : baseEnd_896415 < baseStart_896415 := by decide
  rcases family_descends (prefixWord ++ tailWord_896415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_896522 : List Nat := [3, 1, 2, 2, 2, 2, 3, 1, 5]
def baseStart_896522 : Nat := 118140960795 + 896522 * 2 ^ 59
def prefixEnd_896522 : Nat := 4983230072969 + 3 ^ 40 * 896522 * 2
def baseEnd_896522 : Nat := 204598534813442927667545

theorem tailTrace_896522 : CollatzResearch.WordTrace tailWord_896522 prefixEnd_896522 204598534813442927667545 := by
  unfold tailWord_896522
  simp only [CollatzResearch.WordTrace]
  refine ⟨8174710914515345653174955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21799229105374255075133213 8174710914515345653174955)
  ·
    refine ⟨12262066371773018479762433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8174710914515345653174955 12262066371773018479762433)
    ·
      refine ⟨9196549778829763859821825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12262066371773018479762433 9196549778829763859821825)
      ·
        refine ⟨6897412334122322894866369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9196549778829763859821825 6897412334122322894866369)
        ·
          refine ⟨5173059250591742171149777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6897412334122322894866369 5173059250591742171149777)
          ·
            refine ⟨3879794437943806628362333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5173059250591742171149777 3879794437943806628362333)
            ·
              refine ⟨1454922914228927485635875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3879794437943806628362333 1454922914228927485635875)
              ·
                refine ⟨2182384371343391228453813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1454922914228927485635875 2182384371343391228453813)
                ·
                  refine ⟨204598534813442927667545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2182384371343391228453813 204598534813442927667545)
                  ·
                    rfl

theorem cell21_896522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 3, 1, 5].length) (baseStart_896522 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_896522 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_896522 prefixEnd_896522 := by exact prefixLift 896522
  have htrace : WordTrace (prefixWord ++ tailWord_896522) baseStart_896522 baseEnd_896522 := by
    simpa [prefixWord, tailWord_896522, baseEnd_896522] using wordTrace_append hprefix tailTrace_896522
  have hstable : (prefixWord ++ tailWord_896522).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_896522).length < 2 ^ (prefixWord ++ tailWord_896522).sum := by decide
  have hdescent : baseEnd_896522 < baseStart_896522 := by decide
  rcases family_descends (prefixWord ++ tailWord_896522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_896573 : List Nat := [1, 4, 1, 3, 3, 2, 2, 2, 3]
def baseStart_896573 : Nat := 118140960795 + 896573 * 2 ^ 59
def prefixEnd_896573 : Nat := 4983230072969 + 3 ^ 40 * 896573 * 2
def baseEnd_896573 : Nat := 204610173708278172317441

theorem tailTrace_896573 : CollatzResearch.WordTrace tailWord_896573 prefixEnd_896573 204610173708278172317441 := by
  unfold tailWord_896573
  simp only [CollatzResearch.WordTrace]
  refine ⟨32700703780876618322806373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21800469187251078881870915 32700703780876618322806373)
  ·
    refine ⟨6131381958914365935526195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32700703780876618322806373 6131381958914365935526195)
    ·
      refine ⟨9197072938371548903289293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6131381958914365935526195 9197072938371548903289293)
      ·
        refine ⟨3448902351889330838733485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9197072938371548903289293 3448902351889330838733485)
        ·
          refine ⟨1293338381958499064525057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3448902351889330838733485 1293338381958499064525057)
          ·
            refine ⟨970003786468874298393793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1293338381958499064525057 970003786468874298393793)
            ·
              refine ⟨727502839851655723795345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 970003786468874298393793 727502839851655723795345)
              ·
                refine ⟨545627129888741792846509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 727502839851655723795345 545627129888741792846509)
                ·
                  refine ⟨204610173708278172317441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 545627129888741792846509 204610173708278172317441)
                  ·
                    rfl

theorem cell21_896573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 2, 2, 3].length) (baseStart_896573 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_896573 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_896573 prefixEnd_896573 := by exact prefixLift 896573
  have htrace : WordTrace (prefixWord ++ tailWord_896573) baseStart_896573 baseEnd_896573 := by
    simpa [prefixWord, tailWord_896573, baseEnd_896573] using wordTrace_append hprefix tailTrace_896573
  have hstable : (prefixWord ++ tailWord_896573).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_896573).length < 2 ^ (prefixWord ++ tailWord_896573).sum := by decide
  have hdescent : baseEnd_896573 < baseStart_896573 := by decide
  rcases family_descends (prefixWord ++ tailWord_896573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_896581 : List Nat := [1, 3, 1, 1, 1, 4, 2, 3, 5]
def baseStart_896581 : Nat := 118140960795 + 896581 * 2 ^ 59
def prefixEnd_896581 : Nat := 4983230072969 + 3 ^ 40 * 896581 * 2
def baseEnd_896581 : Nat := 204611999417271936184091

theorem tailTrace_896581 : CollatzResearch.WordTrace tailWord_896581 prefixEnd_896581 204611999417271936184091 := by
  unfold tailWord_896581
  simp only [CollatzResearch.WordTrace]
  refine ⟨32700995564847635689097597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21800663709898423792731731 32700995564847635689097597)
  ·
    refine ⟨12262873336817863383411599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32700995564847635689097597 12262873336817863383411599)
    ·
      refine ⟨18394310005226795075117399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12262873336817863383411599 18394310005226795075117399)
      ·
        refine ⟨27591465007840192612676099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18394310005226795075117399 27591465007840192612676099)
        ·
          refine ⟨41387197511760288919014149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27591465007840192612676099 41387197511760288919014149)
          ·
            refine ⟨7760099533455054172315153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41387197511760288919014149 7760099533455054172315153)
            ·
              refine ⟨5820074650091290629236365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7760099533455054172315153 5820074650091290629236365)
              ·
                refine ⟨2182527993784233985963637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5820074650091290629236365 2182527993784233985963637)
                ·
                  refine ⟨204611999417271936184091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2182527993784233985963637 204611999417271936184091)
                  ·
                    rfl

theorem cell21_896581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 3, 5].length) (baseStart_896581 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_896581 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_896581 prefixEnd_896581 := by exact prefixLift 896581
  have htrace : WordTrace (prefixWord ++ tailWord_896581) baseStart_896581 baseEnd_896581 := by
    simpa [prefixWord, tailWord_896581, baseEnd_896581] using wordTrace_append hprefix tailTrace_896581
  have hstable : (prefixWord ++ tailWord_896581).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_896581).length < 2 ^ (prefixWord ++ tailWord_896581).sum := by decide
  have hdescent : baseEnd_896581 < baseStart_896581 := by decide
  rcases family_descends (prefixWord ++ tailWord_896581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_896629 : List Nat := [1, 3, 4, 2, 1, 2, 1, 1, 6]
def baseStart_896629 : Nat := 118140960795 + 896629 * 2 ^ 59
def prefixEnd_896629 : Nat := 4983230072969 + 3 ^ 40 * 896629 * 2
def baseEnd_896629 : Nat := 204622953671234519383993

theorem tailTrace_896629 : CollatzResearch.WordTrace tailWord_896629 prefixEnd_896629 204622953671234519383993 := by
  unfold tailWord_896629
  simp only [CollatzResearch.WordTrace]
  refine ⟨32702746268673739886844941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21801830845782493257896627 32702746268673739886844941)
  ·
    refine ⟨12263529850752652457566853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32702746268673739886844941 12263529850752652457566853)
    ·
      refine ⟨2299411847016122335793785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12263529850752652457566853 2299411847016122335793785)
      ·
        refine ⟨1724558885262091751845339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2299411847016122335793785 1724558885262091751845339)
        ·
          refine ⟨2586838327893137627768009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1724558885262091751845339 2586838327893137627768009)
          ·
            refine ⟨1940128745919853220826007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2586838327893137627768009 1940128745919853220826007)
            ·
              refine ⟨2910193118879779831239011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1940128745919853220826007 2910193118879779831239011)
              ·
                refine ⟨4365289678319669746858517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2910193118879779831239011 4365289678319669746858517)
                ·
                  refine ⟨204622953671234519383993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4365289678319669746858517 204622953671234519383993)
                  ·
                    rfl

theorem cell21_896629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 1, 1, 6].length) (baseStart_896629 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_896629 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_896629 prefixEnd_896629 := by exact prefixLift 896629
  have htrace : WordTrace (prefixWord ++ tailWord_896629) baseStart_896629 baseEnd_896629 := by
    simpa [prefixWord, tailWord_896629, baseEnd_896629] using wordTrace_append hprefix tailTrace_896629
  have hstable : (prefixWord ++ tailWord_896629).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_896629).length < 2 ^ (prefixWord ++ tailWord_896629).sum := by decide
  have hdescent : baseEnd_896629 < baseStart_896629 := by decide
  rcases family_descends (prefixWord ++ tailWord_896629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_896660 : List Nat := [2, 4, 2, 2, 2, 1, 1, 7]
def baseStart_896660 : Nat := 118140960795 + 896660 * 2 ^ 59
def prefixEnd_896660 : Nat := 4983230072969 + 3 ^ 40 * 896660 * 2
def baseEnd_896660 : Nat := 68210009431195118122421

theorem tailTrace_896660 : CollatzResearch.WordTrace tailWord_896660 prefixEnd_896660 68210009431195118122421 := by
  unfold tailWord_896660
  simp only [CollatzResearch.WordTrace]
  refine ⟨16351938465780716090611717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21802584621040954787482289 16351938465780716090611717)
  ·
    refine ⟨3065988462333884266989697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16351938465780716090611717 3065988462333884266989697)
    ·
      refine ⟨2299491346750413200242273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3065988462333884266989697 2299491346750413200242273)
      ·
        refine ⟨1724618510062809900181705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2299491346750413200242273 1724618510062809900181705)
        ·
          refine ⟨1293463882547107425136279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1724618510062809900181705 1293463882547107425136279)
          ·
            refine ⟨1940195823820661137704419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1293463882547107425136279 1940195823820661137704419)
            ·
              refine ⟨2910293735730991706556629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1940195823820661137704419 2910293735730991706556629)
              ·
                refine ⟨68210009431195118122421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2910293735730991706556629 68210009431195118122421)
                ·
                  rfl

theorem cell21_896660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 1, 7].length) (baseStart_896660 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_896660 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_896660 prefixEnd_896660 := by exact prefixLift 896660
  have htrace : WordTrace (prefixWord ++ tailWord_896660) baseStart_896660 baseEnd_896660 := by
    simpa [prefixWord, tailWord_896660, baseEnd_896660] using wordTrace_append hprefix tailTrace_896660
  have hstable : (prefixWord ++ tailWord_896660).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_896660).length < 2 ^ (prefixWord ++ tailWord_896660).sum := by decide
  have hdescent : baseEnd_896660 < baseStart_896660 := by decide
  rcases family_descends (prefixWord ++ tailWord_896660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_896691 : List Nat := [1, 1, 1, 2, 3, 3, 5, 2, 3]
def baseStart_896691 : Nat := 118140960795 + 896691 * 2 ^ 59
def prefixEnd_896691 : Nat := 4983230072969 + 3 ^ 40 * 896691 * 2
def baseEnd_896691 : Nat := 204637102915936189350533

theorem tailTrace_896691 : CollatzResearch.WordTrace tailWord_896691 prefixEnd_896691 204637102915936189350533 := by
  unfold tailWord_896691
  simp only [CollatzResearch.WordTrace]
  refine ⟨32705007594449124475601927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21803338396299416317067951 32705007594449124475601927)
  ·
    refine ⟨49057511391673686713402891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32705007594449124475601927 49057511391673686713402891)
    ·
      refine ⟨73586267087510530070104337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49057511391673686713402891 73586267087510530070104337)
      ·
        refine ⟨55189700315632897552578253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73586267087510530070104337 55189700315632897552578253)
        ·
          refine ⟨20696137618362336582216845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55189700315632897552578253 20696137618362336582216845)
          ·
            refine ⟨7761051606885876218331317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20696137618362336582216845 7761051606885876218331317)
            ·
              refine ⟨727598588145550895468561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7761051606885876218331317 727598588145550895468561)
              ·
                refine ⟨545698941109163171601421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 727598588145550895468561 545698941109163171601421)
                ·
                  refine ⟨204637102915936189350533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 545698941109163171601421 204637102915936189350533)
                  ·
                    rfl

theorem cell21_896691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 5, 2, 3].length) (baseStart_896691 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_896691 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_896691 prefixEnd_896691 := by exact prefixLift 896691
  have htrace : WordTrace (prefixWord ++ tailWord_896691) baseStart_896691 baseEnd_896691 := by
    simpa [prefixWord, tailWord_896691, baseEnd_896691] using wordTrace_append hprefix tailTrace_896691
  have hstable : (prefixWord ++ tailWord_896691).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_896691).length < 2 ^ (prefixWord ++ tailWord_896691).sum := by decide
  have hdescent : baseEnd_896691 < baseStart_896691 := by decide
  rcases family_descends (prefixWord ++ tailWord_896691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
