import V185TrunkScan22Chunk018

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_170410 : List Nat := [3, 1, 6, 1, 2, 1, 1, 3, 4]
def baseStart_170410 : Nat := 118140960795 + 170410 * 2 ^ 59
def prefixEnd_170410 : Nat := 4983230072969 + 3 ^ 40 * 170410 * 2
def baseEnd_170410 : Nat := 19444941851729667509179

theorem tailTrace_170410 : CollatzResearch.WordTrace tailWord_170410 prefixEnd_170410 19444941851729667509179 := by
  unfold tailWord_170410
  simp only [CollatzResearch.WordTrace]
  refine ⟨1553840828160287139011171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4143575541760765704029789 1553840828160287139011171)
  ·
    refine ⟨2330761242240430708516757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1553840828160287139011171 2330761242240430708516757)
    ·
      refine ⟨109254433230020189461723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 2330761242240430708516757 109254433230020189461723)
      ·
        refine ⟨163881649845030284192585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109254433230020189461723 163881649845030284192585)
        ·
          refine ⟨122911237383772713144439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 163881649845030284192585 122911237383772713144439)
          ·
            refine ⟨184366856075659069716659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122911237383772713144439 184366856075659069716659)
            ·
              refine ⟨276550284113488604574989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 184366856075659069716659 276550284113488604574989)
              ·
                refine ⟨103706356542558226715621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 276550284113488604574989 103706356542558226715621)
                ·
                  refine ⟨19444941851729667509179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 103706356542558226715621 19444941851729667509179)
                  ·
                    rfl

theorem cell22_170410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 1, 3, 4].length) (baseStart_170410 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_170410 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_170410 prefixEnd_170410 := by exact prefixLift 170410
  have htrace : WordTrace (prefixWord ++ tailWord_170410) baseStart_170410 baseEnd_170410 := by
    simpa [prefixWord, tailWord_170410, baseEnd_170410] using wordTrace_append hprefix tailTrace_170410
  have hstable : (prefixWord ++ tailWord_170410).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170410).length < 2 ^ (prefixWord ++ tailWord_170410).sum := by decide
  have hdescent : baseEnd_170410 < baseStart_170410 := by decide
  rcases family_descends (prefixWord ++ tailWord_170410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170430 : List Nat := [4, 2, 1, 1, 1, 1, 2, 1, 4, 5]
def baseStart_170430 : Nat := 118140960795 + 170430 * 2 ^ 59
def prefixEnd_170430 : Nat := 4983230072969 + 3 ^ 40 * 170430 * 2
def baseEnd_170430 : Nat := 58341671963915617027475

theorem tailTrace_170430 : CollatzResearch.WordTrace tailWord_170430 prefixEnd_170430 58341671963915617027475 := by
  unfold tailWord_170430
  simp only [CollatzResearch.WordTrace]
  refine ⟨777011596571086496471593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4144061848379127981181829 777011596571086496471593)
  ·
    refine ⟨582758697428314872353695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 777011596571086496471593 582758697428314872353695)
    ·
      refine ⟨874138046142472308530543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 582758697428314872353695 874138046142472308530543)
      ·
        refine ⟨1311207069213708462795815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 874138046142472308530543 1311207069213708462795815)
        ·
          refine ⟨1966810603820562694193723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1311207069213708462795815 1966810603820562694193723)
          ·
            refine ⟨2950215905730844041290585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1966810603820562694193723 2950215905730844041290585)
            ·
              refine ⟨2212661929298133030967939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2950215905730844041290585 2212661929298133030967939)
              ·
                refine ⟨3318992893947199546451909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2212661929298133030967939 3318992893947199546451909)
                ·
                  refine ⟨622311167615099914959733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3318992893947199546451909 622311167615099914959733)
                  ·
                    refine ⟨58341671963915617027475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 622311167615099914959733 58341671963915617027475)
                    ·
                      rfl

theorem cell22_170430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 1, 4, 5].length) (baseStart_170430 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_170430 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_170430 prefixEnd_170430 := by exact prefixLift 170430
  have htrace : WordTrace (prefixWord ++ tailWord_170430) baseStart_170430 baseEnd_170430 := by
    simpa [prefixWord, tailWord_170430, baseEnd_170430] using wordTrace_append hprefix tailTrace_170430
  have hstable : (prefixWord ++ tailWord_170430).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170430).length < 2 ^ (prefixWord ++ tailWord_170430).sum := by decide
  have hdescent : baseEnd_170430 < baseStart_170430 := by decide
  rcases family_descends (prefixWord ++ tailWord_170430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170436 : List Nat := [2, 3, 3, 2, 2, 2, 1, 1, 3, 3]
def baseStart_170436 : Nat := 118140960795 + 170436 * 2 ^ 59
def prefixEnd_170436 : Nat := 4983230072969 + 3 ^ 40 * 170436 * 2
def baseEnd_170436 : Nat := 58343725886533601377457

theorem tailTrace_170436 : CollatzResearch.WordTrace tailWord_170436 prefixEnd_170436 58343725886533601377457 := by
  unfold tailWord_170436
  simp only [CollatzResearch.WordTrace]
  refine ⟨3108155805273477498245581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4144207740364636664327441 3108155805273477498245581)
  ·
    refine ⟨1165558426977554061842093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3108155805273477498245581 1165558426977554061842093)
    ·
      refine ⟨437084410116582773190785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1165558426977554061842093 437084410116582773190785)
      ·
        refine ⟨327813307587437079893089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 437084410116582773190785 327813307587437079893089)
        ·
          refine ⟨245859980690577809919817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 327813307587437079893089 245859980690577809919817)
          ·
            refine ⟨184394985517933357439863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 245859980690577809919817 184394985517933357439863)
            ·
              refine ⟨276592478276900036159795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 184394985517933357439863 276592478276900036159795)
              ·
                refine ⟨414888717415350054239693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 276592478276900036159795 414888717415350054239693)
                ·
                  refine ⟨155583269030756270339885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 414888717415350054239693 155583269030756270339885)
                  ·
                    refine ⟨58343725886533601377457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 155583269030756270339885 58343725886533601377457)
                    ·
                      rfl

theorem cell22_170436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 1, 1, 3, 3].length) (baseStart_170436 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_170436 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_170436 prefixEnd_170436 := by exact prefixLift 170436
  have htrace : WordTrace (prefixWord ++ tailWord_170436) baseStart_170436 baseEnd_170436 := by
    simpa [prefixWord, tailWord_170436, baseEnd_170436] using wordTrace_append hprefix tailTrace_170436
  have hstable : (prefixWord ++ tailWord_170436).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170436).length < 2 ^ (prefixWord ++ tailWord_170436).sum := by decide
  have hdescent : baseEnd_170436 < baseStart_170436 := by decide
  rcases family_descends (prefixWord ++ tailWord_170436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170475 : List Nat := [1, 1, 1, 1, 2, 3, 5, 2, 1, 5]
def baseStart_170475 : Nat := 118140960795 + 170475 * 2 ^ 59
def prefixEnd_170475 : Nat := 4983230072969 + 3 ^ 40 * 170475 * 2
def baseEnd_170475 : Nat := 58357076383550499652337

theorem tailTrace_170475 : CollatzResearch.WordTrace tailWord_170475 prefixEnd_170475 58357076383550499652337 := by
  unfold tailWord_170475
  simp only [CollatzResearch.WordTrace]
  refine ⟨6217734057405664657160879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4145156038270443104773919 6217734057405664657160879)
  ·
    refine ⟨9326601086108496985741319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6217734057405664657160879 9326601086108496985741319)
    ·
      refine ⟨13989901629162745478611979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9326601086108496985741319 13989901629162745478611979)
      ·
        refine ⟨20984852443744118217917969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13989901629162745478611979 20984852443744118217917969)
        ·
          refine ⟨15738639332808088663438477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20984852443744118217917969 15738639332808088663438477)
          ·
            refine ⟨5901989749803033248789429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15738639332808088663438477 5901989749803033248789429)
            ·
              refine ⟨553311539044034367074009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5901989749803033248789429 553311539044034367074009)
              ·
                refine ⟨414983654283025775305507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 553311539044034367074009 414983654283025775305507)
                ·
                  refine ⟨622475481424538662958261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 414983654283025775305507 622475481424538662958261)
                  ·
                    refine ⟨58357076383550499652337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 622475481424538662958261 58357076383550499652337)
                    ·
                      rfl

theorem cell22_170475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 5, 2, 1, 5].length) (baseStart_170475 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_170475 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_170475 prefixEnd_170475 := by exact prefixLift 170475
  have htrace : WordTrace (prefixWord ++ tailWord_170475) baseStart_170475 baseEnd_170475 := by
    simpa [prefixWord, tailWord_170475, baseEnd_170475] using wordTrace_append hprefix tailTrace_170475
  have hstable : (prefixWord ++ tailWord_170475).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170475).length < 2 ^ (prefixWord ++ tailWord_170475).sum := by decide
  have hdescent : baseEnd_170475 < baseStart_170475 := by decide
  rcases family_descends (prefixWord ++ tailWord_170475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170490 : List Nat := [3, 1, 1, 1, 1, 2, 2, 3, 4, 4]
def baseStart_170490 : Nat := 118140960795 + 170490 * 2 ^ 59
def prefixEnd_170490 : Nat := 4983230072969 + 3 ^ 40 * 170490 * 2
def baseEnd_170490 : Nat := 58362211190095460527291

theorem tailTrace_170490 : CollatzResearch.WordTrace tailWord_170490 prefixEnd_170490 58362211190095460527291 := by
  unfold tailWord_170490
  simp only [CollatzResearch.WordTrace]
  refine ⟨1554570288087830554739231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4145520768234214812637949 1554570288087830554739231)
  ·
    refine ⟨2331855432131745832108847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1554570288087830554739231 2331855432131745832108847)
    ·
      refine ⟨3497783148197618748163271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2331855432131745832108847 3497783148197618748163271)
      ·
        refine ⟨5246674722296428122244907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3497783148197618748163271 5246674722296428122244907)
        ·
          refine ⟨7870012083444642183367361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5246674722296428122244907 7870012083444642183367361)
          ·
            refine ⟨5902509062583481637525521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7870012083444642183367361 5902509062583481637525521)
            ·
              refine ⟨4426881796937611228144141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5902509062583481637525521 4426881796937611228144141)
              ·
                refine ⟨1660080673851604210554053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4426881796937611228144141 1660080673851604210554053)
                ·
                  refine ⟨311265126347175789478885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1660080673851604210554053 311265126347175789478885)
                  ·
                    refine ⟨58362211190095460527291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 311265126347175789478885 58362211190095460527291)
                    ·
                      rfl

theorem cell22_170490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 3, 4, 4].length) (baseStart_170490 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_170490 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_170490 prefixEnd_170490 := by exact prefixLift 170490
  have htrace : WordTrace (prefixWord ++ tailWord_170490) baseStart_170490 baseEnd_170490 := by
    simpa [prefixWord, tailWord_170490, baseEnd_170490] using wordTrace_append hprefix tailTrace_170490
  have hstable : (prefixWord ++ tailWord_170490).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170490).length < 2 ^ (prefixWord ++ tailWord_170490).sum := by decide
  have hdescent : baseEnd_170490 < baseStart_170490 := by decide
  rcases family_descends (prefixWord ++ tailWord_170490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170524 : List Nat := [2, 2, 3, 1, 2, 4, 1, 1, 2, 4]
def baseStart_170524 : Nat := 118140960795 + 170524 * 2 ^ 59
def prefixEnd_170524 : Nat := 4983230072969 + 3 ^ 40 * 170524 * 2
def baseEnd_170524 : Nat := 58373850084930705177187

theorem tailTrace_170524 : CollatzResearch.WordTrace tailWord_170524 prefixEnd_170524 58373850084930705177187 := by
  unfold tailWord_170524
  simp only [CollatzResearch.WordTrace]
  refine ⟨3109760617114073012847313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4146347489485430683796417 3109760617114073012847313)
  ·
    refine ⟨2332320462835554759635485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3109760617114073012847313 2332320462835554759635485)
    ·
      refine ⟨874620173563333034863307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2332320462835554759635485 874620173563333034863307)
      ·
        refine ⟨1311930260344999552294961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 874620173563333034863307 1311930260344999552294961)
        ·
          refine ⟨983947695258749664221221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1311930260344999552294961 983947695258749664221221)
          ·
            refine ⟨184490192861015562041479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 983947695258749664221221 184490192861015562041479)
            ·
              refine ⟨276735289291523343062219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 184490192861015562041479 276735289291523343062219)
              ·
                refine ⟨415102933937285014593329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 276735289291523343062219 415102933937285014593329)
                ·
                  refine ⟨311327200452963760944997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 415102933937285014593329 311327200452963760944997)
                  ·
                    refine ⟨58373850084930705177187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 311327200452963760944997 58373850084930705177187)
                    ·
                      rfl

theorem cell22_170524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 1, 1, 2, 4].length) (baseStart_170524 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_170524 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_170524 prefixEnd_170524 := by exact prefixLift 170524
  have htrace : WordTrace (prefixWord ++ tailWord_170524) baseStart_170524 baseEnd_170524 := by
    simpa [prefixWord, tailWord_170524, baseEnd_170524] using wordTrace_append hprefix tailTrace_170524
  have hstable : (prefixWord ++ tailWord_170524).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170524).length < 2 ^ (prefixWord ++ tailWord_170524).sum := by decide
  have hdescent : baseEnd_170524 < baseStart_170524 := by decide
  rcases family_descends (prefixWord ++ tailWord_170524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170554 : List Nat := [3, 1, 1, 1, 3, 4, 2, 1, 3, 3]
def baseStart_170554 : Nat := 118140960795 + 170554 * 2 ^ 59
def prefixEnd_170554 : Nat := 4983230072969 + 3 ^ 40 * 170554 * 2
def baseEnd_170554 : Nat := 58384119698020626927095

theorem tailTrace_170554 : CollatzResearch.WordTrace tailWord_170554 prefixEnd_170554 58384119698020626927095 := by
  unfold tailWord_170554
  simp only [CollatzResearch.WordTrace]
  refine ⟨1555153856029865287321679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4147076949412974099524477 1555153856029865287321679)
  ·
    refine ⟨2332730784044797930982519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1555153856029865287321679 2332730784044797930982519)
    ·
      refine ⟨3499096176067196896473779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2332730784044797930982519 3499096176067196896473779)
      ·
        refine ⟨5248644264100795344710669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3499096176067196896473779 5248644264100795344710669)
        ·
          refine ⟨1968241599037798254266501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5248644264100795344710669 1968241599037798254266501)
          ·
            refine ⟨369045299819587172674969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1968241599037798254266501 369045299819587172674969)
            ·
              refine ⟨276783974864690379506227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 369045299819587172674969 276783974864690379506227)
              ·
                refine ⟨415175962297035569259341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 276783974864690379506227 415175962297035569259341)
                ·
                  refine ⟨155690985861388338472253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 415175962297035569259341 155690985861388338472253)
                  ·
                    refine ⟨58384119698020626927095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 155690985861388338472253 58384119698020626927095)
                    ·
                      rfl

theorem cell22_170554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 2, 1, 3, 3].length) (baseStart_170554 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_170554 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_170554 prefixEnd_170554 := by exact prefixLift 170554
  have htrace : WordTrace (prefixWord ++ tailWord_170554) baseStart_170554 baseEnd_170554 := by
    simpa [prefixWord, tailWord_170554, baseEnd_170554] using wordTrace_append hprefix tailTrace_170554
  have hstable : (prefixWord ++ tailWord_170554).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170554).length < 2 ^ (prefixWord ++ tailWord_170554).sum := by decide
  have hdescent : baseEnd_170554 < baseStart_170554 := by decide
  rcases family_descends (prefixWord ++ tailWord_170554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170644 : List Nat := [2, 4, 2, 2, 1, 1, 1, 1, 3, 5]
def baseStart_170644 : Nat := 118140960795 + 170644 * 2 ^ 59
def prefixEnd_170644 : Nat := 4983230072969 + 3 ^ 40 * 170644 * 2
def baseEnd_170644 : Nat := 58414928537290392176819

theorem tailTrace_170644 : CollatzResearch.WordTrace tailWord_170644 prefixEnd_170644 58414928537290392176819 := by
  unfold tailWord_170644
  simp only [CollatzResearch.WordTrace]
  refine ⟨3111948996896703260031493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4149265329195604346708657 3111948996896703260031493)
  ·
    refine ⟨583490436918131861255905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3111948996896703260031493 583490436918131861255905)
    ·
      refine ⟨437617827688598895941929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 583490436918131861255905 437617827688598895941929)
      ·
        refine ⟨328213370766449171956447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 437617827688598895941929 328213370766449171956447)
        ·
          refine ⟨492320056149673757934671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 328213370766449171956447 492320056149673757934671)
          ·
            refine ⟨738480084224510636902007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 492320056149673757934671 738480084224510636902007)
            ·
              refine ⟨1107720126336765955353011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 738480084224510636902007 1107720126336765955353011)
              ·
                refine ⟨1661580189505148933029517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1107720126336765955353011 1661580189505148933029517)
                ·
                  refine ⟨623092571064430849886069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1661580189505148933029517 623092571064430849886069)
                  ·
                    refine ⟨58414928537290392176819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 623092571064430849886069 58414928537290392176819)
                    ·
                      rfl

theorem cell22_170644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 1, 3, 5].length) (baseStart_170644 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_170644 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_170644 prefixEnd_170644 := by exact prefixLift 170644
  have htrace : WordTrace (prefixWord ++ tailWord_170644) baseStart_170644 baseEnd_170644 := by
    simpa [prefixWord, tailWord_170644, baseEnd_170644] using wordTrace_append hprefix tailTrace_170644
  have hstable : (prefixWord ++ tailWord_170644).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170644).length < 2 ^ (prefixWord ++ tailWord_170644).sum := by decide
  have hdescent : baseEnd_170644 < baseStart_170644 := by decide
  rcases family_descends (prefixWord ++ tailWord_170644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170657 : List Nat := [1, 2, 3, 3, 3, 10]
def baseStart_170657 : Nat := 118140960795 + 170657 * 2 ^ 59
def prefixEnd_170657 : Nat := 4983230072969 + 3 ^ 40 * 170657 * 2
def baseEnd_170657 : Nat := 721226897567440637059

theorem tailTrace_170657 : CollatzResearch.WordTrace tailWord_170657 prefixEnd_170657 721226897567440637059 := by
  unfold tailWord_170657
  simp only [CollatzResearch.WordTrace]
  refine ⟨6224372142746309740286225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4149581428497539826857483 6224372142746309740286225)
  ·
    refine ⟨4668279107059732305214669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6224372142746309740286225 4668279107059732305214669)
    ·
      refine ⟨1750604665147399614455501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4668279107059732305214669 1750604665147399614455501)
      ·
        refine ⟨656476749430274855420813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1750604665147399614455501 656476749430274855420813)
        ·
          refine ⟨246178781036353070782805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 656476749430274855420813 246178781036353070782805)
          ·
            refine ⟨721226897567440637059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 246178781036353070782805 721226897567440637059)
            ·
              rfl

theorem cell22_170657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 10].length) (baseStart_170657 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_170657 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_170657 prefixEnd_170657 := by exact prefixLift 170657
  have htrace : WordTrace (prefixWord ++ tailWord_170657) baseStart_170657 baseEnd_170657 := by
    simpa [prefixWord, tailWord_170657, baseEnd_170657] using wordTrace_append hprefix tailTrace_170657
  have hstable : (prefixWord ++ tailWord_170657).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170657).length < 2 ^ (prefixWord ++ tailWord_170657).sum := by decide
  have hdescent : baseEnd_170657 < baseStart_170657 := by decide
  rcases family_descends (prefixWord ++ tailWord_170657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170663 : List Nat := [1, 1, 6, 3, 1, 1, 1, 4, 4]
def baseStart_170663 : Nat := 118140960795 + 170663 * 2 ^ 59
def prefixEnd_170663 : Nat := 4983230072969 + 3 ^ 40 * 170663 * 2
def baseEnd_170663 : Nat := 19473810875193558650587

theorem tailTrace_170663 : CollatzResearch.WordTrace tailWord_170663 prefixEnd_170663 19473810875193558650587 := by
  unfold tailWord_170663
  simp only [CollatzResearch.WordTrace]
  refine ⟨6224590980724572765004643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4149727320483048510003095 6224590980724572765004643)
  ·
    refine ⟨9336886471086859147506965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6224590980724572765004643 9336886471086859147506965)
    ·
      refine ⟨437666553332196522539389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 9336886471086859147506965 437666553332196522539389)
      ·
        refine ⟨164124957499573695952271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 437666553332196522539389 164124957499573695952271)
        ·
          refine ⟨246187436249360543928407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164124957499573695952271 246187436249360543928407)
          ·
            refine ⟨369281154374040815892611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 246187436249360543928407 369281154374040815892611)
            ·
              refine ⟨553921731561061223838917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 369281154374040815892611 553921731561061223838917)
              ·
                refine ⟨103860324667698979469797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 553921731561061223838917 103860324667698979469797)
                ·
                  refine ⟨19473810875193558650587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 103860324667698979469797 19473810875193558650587)
                  ·
                    rfl

theorem cell22_170663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 1, 4, 4].length) (baseStart_170663 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_170663 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_170663 prefixEnd_170663 := by exact prefixLift 170663
  have htrace : WordTrace (prefixWord ++ tailWord_170663) baseStart_170663 baseEnd_170663 := by
    simpa [prefixWord, tailWord_170663, baseEnd_170663] using wordTrace_append hprefix tailTrace_170663
  have hstable : (prefixWord ++ tailWord_170663).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170663).length < 2 ^ (prefixWord ++ tailWord_170663).sum := by decide
  have hdescent : baseEnd_170663 < baseStart_170663 := by decide
  rcases family_descends (prefixWord ++ tailWord_170663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170678 : List Nat := [5, 1, 3, 1, 2, 1, 2, 1, 1, 5]
def baseStart_170678 : Nat := 118140960795 + 170678 * 2 ^ 59
def prefixEnd_170678 : Nat := 4983230072969 + 3 ^ 40 * 170678 * 2
def baseEnd_170678 : Nat := 58426567432125636826715

theorem tailTrace_170678 : CollatzResearch.WordTrace tailWord_170678 prefixEnd_170678 58426567432125636826715 := by
  unfold tailWord_170678
  simp only [CollatzResearch.WordTrace]
  refine ⟨389071129729389395425043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4150092050446820217867125 389071129729389395425043)
  ·
    refine ⟨583606694594084093137565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 389071129729389395425043 583606694594084093137565)
    ·
      refine ⟨218852510472781534926587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 583606694594084093137565 218852510472781534926587)
      ·
        refine ⟨328278765709172302389881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 218852510472781534926587 328278765709172302389881)
        ·
          refine ⟨246209074281879226792411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 328278765709172302389881 246209074281879226792411)
          ·
            refine ⟨369313611422818840188617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 246209074281879226792411 369313611422818840188617)
            ·
              refine ⟨276985208567114130141463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 369313611422818840188617 276985208567114130141463)
              ·
                refine ⟨415477812850671195212195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 276985208567114130141463 415477812850671195212195)
                ·
                  refine ⟨623216719276006792818293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 415477812850671195212195 623216719276006792818293)
                  ·
                    refine ⟨58426567432125636826715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 623216719276006792818293 58426567432125636826715)
                    ·
                      rfl

theorem cell22_170678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 2, 1, 1, 5].length) (baseStart_170678 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_170678 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_170678 prefixEnd_170678 := by exact prefixLift 170678
  have htrace : WordTrace (prefixWord ++ tailWord_170678) baseStart_170678 baseEnd_170678 := by
    simpa [prefixWord, tailWord_170678, baseEnd_170678] using wordTrace_append hprefix tailTrace_170678
  have hstable : (prefixWord ++ tailWord_170678).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170678).length < 2 ^ (prefixWord ++ tailWord_170678).sum := by decide
  have hdescent : baseEnd_170678 < baseStart_170678 := by decide
  rcases family_descends (prefixWord ++ tailWord_170678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170719 : List Nat := [1, 1, 2, 3, 2, 3, 3, 2, 5]
def baseStart_170719 : Nat := 118140960795 + 170719 * 2 ^ 59
def prefixEnd_170719 : Nat := 4983230072969 + 3 ^ 40 * 170719 * 2
def baseEnd_170719 : Nat := 19480200856671732183863

theorem tailTrace_170719 : CollatzResearch.WordTrace tailWord_170719 prefixEnd_170719 19480200856671732183863 := by
  unfold tailWord_170719
  simp only [CollatzResearch.WordTrace]
  refine ⟨6226633468521694329043211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4151088979014462886028807 6226633468521694329043211)
  ·
    refine ⟨9339950202782541493564817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6226633468521694329043211 9339950202782541493564817)
    ·
      refine ⟨7004962652086906120173613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9339950202782541493564817 7004962652086906120173613)
      ·
        refine ⟨2626860994532589795065105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7004962652086906120173613 2626860994532589795065105)
        ·
          refine ⟨1970145745899442346298829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2626860994532589795065105 1970145745899442346298829)
          ·
            refine ⟨738804654712290879862061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1970145745899442346298829 738804654712290879862061)
            ·
              refine ⟨277051745517109079948273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 738804654712290879862061 277051745517109079948273)
              ·
                refine ⟨207788809137831809961205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 277051745517109079948273 207788809137831809961205)
                ·
                  refine ⟨19480200856671732183863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 207788809137831809961205 19480200856671732183863)
                  ·
                    rfl

theorem cell22_170719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 3, 2, 5].length) (baseStart_170719 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_170719 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_170719 prefixEnd_170719 := by exact prefixLift 170719
  have htrace : WordTrace (prefixWord ++ tailWord_170719) baseStart_170719 baseEnd_170719 := by
    simpa [prefixWord, tailWord_170719, baseEnd_170719] using wordTrace_append hprefix tailTrace_170719
  have hstable : (prefixWord ++ tailWord_170719).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170719).length < 2 ^ (prefixWord ++ tailWord_170719).sum := by decide
  have hdescent : baseEnd_170719 < baseStart_170719 := by decide
  rcases family_descends (prefixWord ++ tailWord_170719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170723 : List Nat := [1, 1, 1, 7, 1, 1, 2, 4, 1, 3]
def baseStart_170723 : Nat := 118140960795 + 170723 * 2 ^ 59
def prefixEnd_170723 : Nat := 4983230072969 + 3 ^ 40 * 170723 * 2
def baseEnd_170723 : Nat := 58441971851760519451577

theorem tailTrace_170723 : CollatzResearch.WordTrace tailWord_170723 prefixEnd_170723 58441971851760519451577 := by
  unfold tailWord_170723
  simp only [CollatzResearch.WordTrace]
  refine ⟨6226779360507203012188823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4151186240338135341459215 6226779360507203012188823)
  ·
    refine ⟨9340169040760804518283235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6226779360507203012188823 9340169040760804518283235)
    ·
      refine ⟨14010253561141206777424853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9340169040760804518283235 14010253561141206777424853)
      ·
        refine ⟨328365317839247033845895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 14010253561141206777424853 328365317839247033845895)
        ·
          refine ⟨492547976758870550768843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 328365317839247033845895 492547976758870550768843)
          ·
            refine ⟨738821965138305826153265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 492547976758870550768843 738821965138305826153265)
            ·
              refine ⟨554116473853729369614949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 738821965138305826153265 554116473853729369614949)
              ·
                refine ⟨103896838847574256802803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 554116473853729369614949 103896838847574256802803)
                ·
                  refine ⟨155845258271361385204205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 103896838847574256802803 155845258271361385204205)
                  ·
                    refine ⟨58441971851760519451577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 155845258271361385204205 58441971851760519451577)
                    ·
                      rfl

theorem cell22_170723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 2, 4, 1, 3].length) (baseStart_170723 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_170723 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_170723 prefixEnd_170723 := by exact prefixLift 170723
  have htrace : WordTrace (prefixWord ++ tailWord_170723) baseStart_170723 baseEnd_170723 := by
    simpa [prefixWord, tailWord_170723, baseEnd_170723] using wordTrace_append hprefix tailTrace_170723
  have hstable : (prefixWord ++ tailWord_170723).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170723).length < 2 ^ (prefixWord ++ tailWord_170723).sum := by decide
  have hdescent : baseEnd_170723 < baseStart_170723 := by decide
  rcases family_descends (prefixWord ++ tailWord_170723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170734 : List Nat := [4, 1, 2, 1, 1, 3, 2, 1, 2, 5]
def baseStart_170734 : Nat := 118140960795 + 170734 * 2 ^ 59
def prefixEnd_170734 : Nat := 4983230072969 + 3 ^ 40 * 170734 * 2
def baseEnd_170734 : Nat := 58445737376560157426543

theorem tailTrace_170734 : CollatzResearch.WordTrace tailWord_170734 prefixEnd_170734 58445737376560157426543 := by
  unfold tailWord_170734
  simp only [CollatzResearch.WordTrace]
  refine ⟨778397570433418986354907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4151453708978234593892837 778397570433418986354907)
  ·
    refine ⟨1167596355650128479532361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 778397570433418986354907 1167596355650128479532361)
    ·
      refine ⟨875697266737596359649271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1167596355650128479532361 875697266737596359649271)
      ·
        refine ⟨1313545900106394539473907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 875697266737596359649271 1313545900106394539473907)
        ·
          refine ⟨1970318850159591809210861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1313545900106394539473907 1970318850159591809210861)
          ·
            refine ⟨738869568809846928454073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1970318850159591809210861 738869568809846928454073)
            ·
              refine ⟨554152176607385196340555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 738869568809846928454073 554152176607385196340555)
              ·
                refine ⟨831228264911077794510833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 554152176607385196340555 831228264911077794510833)
                ·
                  refine ⟨623421198683308345883125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 831228264911077794510833 623421198683308345883125)
                  ·
                    refine ⟨58445737376560157426543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 623421198683308345883125 58445737376560157426543)
                    ·
                      rfl

theorem cell22_170734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 2, 1, 2, 5].length) (baseStart_170734 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_170734 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_170734 prefixEnd_170734 := by exact prefixLift 170734
  have htrace : WordTrace (prefixWord ++ tailWord_170734) baseStart_170734 baseEnd_170734 := by
    simpa [prefixWord, tailWord_170734, baseEnd_170734] using wordTrace_append hprefix tailTrace_170734
  have hstable : (prefixWord ++ tailWord_170734).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170734).length < 2 ^ (prefixWord ++ tailWord_170734).sum := by decide
  have hdescent : baseEnd_170734 < baseStart_170734 := by decide
  rcases family_descends (prefixWord ++ tailWord_170734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170777 : List Nat := [1, 2, 1, 2, 1, 1, 1, 4, 3, 6]
def baseStart_170777 : Nat := 118140960795 + 170777 * 2 ^ 59
def prefixEnd_170777 : Nat := 4983230072969 + 3 ^ 40 * 170777 * 2
def baseEnd_170777 : Nat := 58460457155322378601411

theorem tailTrace_170777 : CollatzResearch.WordTrace tailWord_170777 prefixEnd_170777 58460457155322378601411 := by
  unfold tailWord_170777
  simp only [CollatzResearch.WordTrace]
  refine ⟨6228748902311570234654585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4152499268207713489769723 6228748902311570234654585)
  ·
    refine ⟨4671561676733677675990939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6228748902311570234654585 4671561676733677675990939)
    ·
      refine ⟨7007342515100516513986409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4671561676733677675990939 7007342515100516513986409)
      ·
        refine ⟨5255506886325387385489807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7007342515100516513986409 5255506886325387385489807)
        ·
          refine ⟨7883260329488081078234711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5255506886325387385489807 7883260329488081078234711)
          ·
            refine ⟨11824890494232121617352067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7883260329488081078234711 11824890494232121617352067)
            ·
              refine ⟨17737335741348182426028101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11824890494232121617352067 17737335741348182426028101)
              ·
                refine ⟨3325750451502784204880269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17737335741348182426028101 3325750451502784204880269)
                ·
                  refine ⟨1247156419313544076830101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3325750451502784204880269 1247156419313544076830101)
                  ·
                    refine ⟨58460457155322378601411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1247156419313544076830101 58460457155322378601411)
                    ·
                      rfl

theorem cell22_170777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 4, 3, 6].length) (baseStart_170777 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_170777 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_170777 prefixEnd_170777 := by exact prefixLift 170777
  have htrace : WordTrace (prefixWord ++ tailWord_170777) baseStart_170777 baseEnd_170777 := by
    simpa [prefixWord, tailWord_170777, baseEnd_170777] using wordTrace_append hprefix tailTrace_170777
  have hstable : (prefixWord ++ tailWord_170777).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170777).length < 2 ^ (prefixWord ++ tailWord_170777).sum := by decide
  have hdescent : baseEnd_170777 < baseStart_170777 := by decide
  rcases family_descends (prefixWord ++ tailWord_170777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170796 : List Nat := [2, 2, 1, 1, 1, 4, 3, 3, 2, 3]
def baseStart_170796 : Nat := 118140960795 + 170796 * 2 ^ 59
def prefixEnd_170796 : Nat := 4983230072969 + 3 ^ 40 * 170796 * 2
def baseEnd_170796 : Nat := 58466961243612662376353

theorem tailTrace_170796 : CollatzResearch.WordTrace tailWord_170796 prefixEnd_170796 58466961243612662376353 := by
  unfold tailWord_170796
  simp only [CollatzResearch.WordTrace]
  refine ⟨3114720944621368239798121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4152961259495157653064161 3114720944621368239798121)
  ·
    refine ⟨2336040708466026179848591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3114720944621368239798121 2336040708466026179848591)
    ·
      refine ⟨3504061062699039269772887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2336040708466026179848591 3504061062699039269772887)
      ·
        refine ⟨5256091594048558904659331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3504061062699039269772887 5256091594048558904659331)
        ·
          refine ⟨7884137391072838356988997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5256091594048558904659331 7884137391072838356988997)
          ·
            refine ⟨1478275760826157191935437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7884137391072838356988997 1478275760826157191935437)
            ·
              refine ⟨554353410309808946975789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1478275760826157191935437 554353410309808946975789)
              ·
                refine ⟨207882528866178355115921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 554353410309808946975789 207882528866178355115921)
                ·
                  refine ⟨155911896649633766336941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 207882528866178355115921 155911896649633766336941)
                  ·
                    refine ⟨58466961243612662376353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 155911896649633766336941 58466961243612662376353)
                    ·
                      rfl

theorem cell22_170796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 3].length) (baseStart_170796 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_170796 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_170796 prefixEnd_170796 := by exact prefixLift 170796
  have htrace : WordTrace (prefixWord ++ tailWord_170796) baseStart_170796 baseEnd_170796 := by
    simpa [prefixWord, tailWord_170796, baseEnd_170796] using wordTrace_append hprefix tailTrace_170796
  have hstable : (prefixWord ++ tailWord_170796).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170796).length < 2 ^ (prefixWord ++ tailWord_170796).sum := by decide
  have hdescent : baseEnd_170796 < baseStart_170796 := by decide
  rcases family_descends (prefixWord ++ tailWord_170796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170839 : List Nat := [1, 1, 3, 2, 4, 1, 1, 1, 2, 6]
def baseStart_170839 : Nat := 118140960795 + 170839 * 2 ^ 59
def prefixEnd_170839 : Nat := 4983230072969 + 3 ^ 40 * 170839 * 2
def baseEnd_170839 : Nat := 58481681022374883551221

theorem tailTrace_170839 : CollatzResearch.WordTrace tailWord_170839 prefixEnd_170839 58481681022374883551221 := by
  unfold tailWord_170839
  simp only [CollatzResearch.WordTrace]
  refine ⟨6231010228086954823411571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4154006818724636548941047 6231010228086954823411571)
  ·
    refine ⟨9346515342130432235117357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6231010228086954823411571 9346515342130432235117357)
    ·
      refine ⟨3504943253298912088169009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9346515342130432235117357 3504943253298912088169009)
      ·
        refine ⟨2628707439974184066126757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3504943253298912088169009 2628707439974184066126757)
        ·
          refine ⟨492882644995159512398767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2628707439974184066126757 492882644995159512398767)
          ·
            refine ⟨739323967492739268598151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 492882644995159512398767 739323967492739268598151)
            ·
              refine ⟨1108985951239108902897227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 739323967492739268598151 1108985951239108902897227)
              ·
                refine ⟨1663478926858663354345841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1108985951239108902897227 1663478926858663354345841)
                ·
                  refine ⟨1247609195143997515759381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1663478926858663354345841 1247609195143997515759381)
                  ·
                    refine ⟨58481681022374883551221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1247609195143997515759381 58481681022374883551221)
                    ·
                      rfl

theorem cell22_170839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 1, 2, 6].length) (baseStart_170839 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_170839 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_170839 prefixEnd_170839 := by exact prefixLift 170839
  have htrace : WordTrace (prefixWord ++ tailWord_170839) baseStart_170839 baseEnd_170839 := by
    simpa [prefixWord, tailWord_170839, baseEnd_170839] using wordTrace_append hprefix tailTrace_170839
  have hstable : (prefixWord ++ tailWord_170839).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170839).length < 2 ^ (prefixWord ++ tailWord_170839).sum := by decide
  have hdescent : baseEnd_170839 < baseStart_170839 := by decide
  rcases family_descends (prefixWord ++ tailWord_170839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170888 : List Nat := [2, 1, 3, 3, 2, 3, 1, 2, 5]
def baseStart_170888 : Nat := 118140960795 + 170888 * 2 ^ 59
def prefixEnd_170888 : Nat := 4983230072969 + 3 ^ 40 * 170888 * 2
def baseEnd_170888 : Nat := 19499484907918363025357

theorem tailTrace_170888 : CollatzResearch.WordTrace tailWord_170888 prefixEnd_170888 19499484907918363025357 := by
  unfold tailWord_170888
  simp only [CollatzResearch.WordTrace]
  refine ⟨3116398702454718095972659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4155198269939624127963545 3116398702454718095972659)
  ·
    refine ⟨4674598053682077143958989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3116398702454718095972659 4674598053682077143958989)
    ·
      refine ⟨1752974270130778928984621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4674598053682077143958989 1752974270130778928984621)
      ·
        refine ⟨657365351299042098369233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1752974270130778928984621 657365351299042098369233)
        ·
          refine ⟨493024013474281573776925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 657365351299042098369233 493024013474281573776925)
          ·
            refine ⟨184884005052855590166347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 493024013474281573776925 184884005052855590166347)
            ·
              refine ⟨277326007579283385249521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 184884005052855590166347 277326007579283385249521)
              ·
                refine ⟨207994505684462538937141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 277326007579283385249521 207994505684462538937141)
                ·
                  refine ⟨19499484907918363025357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 207994505684462538937141 19499484907918363025357)
                  ·
                    rfl

theorem cell22_170888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 1, 2, 5].length) (baseStart_170888 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_170888 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_170888 prefixEnd_170888 := by exact prefixLift 170888
  have htrace : WordTrace (prefixWord ++ tailWord_170888) baseStart_170888 baseEnd_170888 := by
    simpa [prefixWord, tailWord_170888, baseEnd_170888] using wordTrace_append hprefix tailTrace_170888
  have hstable : (prefixWord ++ tailWord_170888).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170888).length < 2 ^ (prefixWord ++ tailWord_170888).sum := by decide
  have hdescent : baseEnd_170888 < baseStart_170888 := by decide
  rcases family_descends (prefixWord ++ tailWord_170888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170944 : List Nat := [2, 1, 1, 2, 3, 3, 10]
def baseStart_170944 : Nat := 118140960795 + 170944 * 2 ^ 59
def prefixEnd_170944 : Nat := 4983230072969 + 3 ^ 40 * 170944 * 2
def baseEnd_170944 : Nat := 2167319432155170728737

theorem tailTrace_170944 : CollatzResearch.WordTrace tailWord_170944 prefixEnd_170944 2167319432155170728737 := by
  unfold tailWord_170944
  simp only [CollatzResearch.WordTrace]
  refine ⟨3117419946353278877991943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4156559928471038503989257 3117419946353278877991943)
  ·
    refine ⟨4676129919529918316987915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3117419946353278877991943 4676129919529918316987915)
    ·
      refine ⟨7014194879294877475481873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4676129919529918316987915 7014194879294877475481873)
      ·
        refine ⟨5260646159471158106611405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7014194879294877475481873 5260646159471158106611405)
        ·
          refine ⟨1972742309801684289979277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5260646159471158106611405 1972742309801684289979277)
          ·
            refine ⟨739778366175631608742229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1972742309801684289979277 739778366175631608742229)
            ·
              refine ⟨2167319432155170728737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 739778366175631608742229 2167319432155170728737)
              ·
                rfl

theorem cell22_170944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 10].length) (baseStart_170944 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_170944 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_170944 prefixEnd_170944 := by exact prefixLift 170944
  have htrace : WordTrace (prefixWord ++ tailWord_170944) baseStart_170944 baseEnd_170944 := by
    simpa [prefixWord, tailWord_170944, baseEnd_170944] using wordTrace_append hprefix tailTrace_170944
  have hstable : (prefixWord ++ tailWord_170944).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170944).length < 2 ^ (prefixWord ++ tailWord_170944).sum := by decide
  have hdescent : baseEnd_170944 < baseStart_170944 := by decide
  rcases family_descends (prefixWord ++ tailWord_170944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170965 : List Nat := [1, 3, 2, 3, 3, 1, 1, 3, 2, 3]
def baseStart_170965 : Nat := 118140960795 + 170965 * 2 ^ 59
def prefixEnd_170965 : Nat := 4983230072969 + 3 ^ 40 * 170965 * 2
def baseEnd_170965 : Nat := 58524813397352554900835

theorem tailTrace_170965 : CollatzResearch.WordTrace tailWord_170965 prefixEnd_170965 58524813397352554900835 := by
  unfold tailWord_170965
  simp only [CollatzResearch.WordTrace]
  refine ⟨6235605825630478342498349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4157070550420318894998899 6235605825630478342498349)
  ·
    refine ⟨2338352184611429378436881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6235605825630478342498349 2338352184611429378436881)
    ·
      refine ⟨1753764138458572033827661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2338352184611429378436881 1753764138458572033827661)
      ·
        refine ⟨657661551921964512685373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1753764138458572033827661 657661551921964512685373)
        ·
          refine ⟨246623081970736692257015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 657661551921964512685373 246623081970736692257015)
          ·
            refine ⟨369934622956105038385523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 246623081970736692257015 369934622956105038385523)
            ·
              refine ⟨554901934434157557578285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 369934622956105038385523 554901934434157557578285)
              ·
                refine ⟨208088225412809084091857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 554901934434157557578285 208088225412809084091857)
                ·
                  refine ⟨156066169059606813068893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 208088225412809084091857 156066169059606813068893)
                  ·
                    refine ⟨58524813397352554900835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 156066169059606813068893 58524813397352554900835)
                    ·
                      rfl

theorem cell22_170965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 1, 3, 2, 3].length) (baseStart_170965 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_170965 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_170965 prefixEnd_170965 := by exact prefixLift 170965
  have htrace : WordTrace (prefixWord ++ tailWord_170965) baseStart_170965 baseEnd_170965 := by
    simpa [prefixWord, tailWord_170965, baseEnd_170965] using wordTrace_append hprefix tailTrace_170965
  have hstable : (prefixWord ++ tailWord_170965).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170965).length < 2 ^ (prefixWord ++ tailWord_170965).sum := by decide
  have hdescent : baseEnd_170965 < baseStart_170965 := by decide
  rcases family_descends (prefixWord ++ tailWord_170965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170978 : List Nat := [3, 3, 3, 1, 1, 1, 2, 8]
def baseStart_170978 : Nat := 118140960795 + 170978 * 2 ^ 59
def prefixEnd_170978 : Nat := 4983230072969 + 3 ^ 40 * 170978 * 2
def baseEnd_170978 : Nat := 6503251507002761591755

theorem tailTrace_170978 : CollatzResearch.WordTrace tailWord_170978 prefixEnd_170978 6503251507002761591755 := by
  unfold tailWord_170978
  simp only [CollatzResearch.WordTrace]
  refine ⟨1559019993645845390680397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4157386649722254375147725 1559019993645845390680397)
  ·
    refine ⟨584632497617192021505149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1559019993645845390680397 584632497617192021505149)
    ·
      refine ⟨219237186606447008064431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 584632497617192021505149 219237186606447008064431)
      ·
        refine ⟨328855779909670512096647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 219237186606447008064431 328855779909670512096647)
        ·
          refine ⟨493283669864505768144971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 328855779909670512096647 493283669864505768144971)
          ·
            refine ⟨739925504796758652217457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 493283669864505768144971 739925504796758652217457)
            ·
              refine ⟨554944128597568989163093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 739925504796758652217457 554944128597568989163093)
              ·
                refine ⟨6503251507002761591755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 554944128597568989163093 6503251507002761591755)
                ·
                  rfl

theorem cell22_170978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 2, 8].length) (baseStart_170978 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_170978 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_170978 prefixEnd_170978 := by exact prefixLift 170978
  have htrace : WordTrace (prefixWord ++ tailWord_170978) baseStart_170978 baseEnd_170978 := by
    simpa [prefixWord, tailWord_170978, baseEnd_170978] using wordTrace_append hprefix tailTrace_170978
  have hstable : (prefixWord ++ tailWord_170978).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170978).length < 2 ^ (prefixWord ++ tailWord_170978).sum := by decide
  have hdescent : baseEnd_170978 < baseStart_170978 := by decide
  rcases family_descends (prefixWord ++ tailWord_170978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171066 : List Nat := [3, 1, 1, 1, 3, 1, 2, 2, 3, 5]
def baseStart_171066 : Nat := 118140960795 + 171066 * 2 ^ 59
def prefixEnd_171066 : Nat := 4983230072969 + 3 ^ 40 * 171066 * 2
def baseEnd_171066 : Nat := 58559387761421958125525

theorem tailTrace_171066 : CollatzResearch.WordTrace tailWord_171066 prefixEnd_171066 58559387761421958125525 := by
  unfold tailWord_171066
  simp only [CollatzResearch.WordTrace]
  refine ⟨1559822399566143147981263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4159526398843048394616701 1559822399566143147981263)
  ·
    refine ⟨2339733599349214721971895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1559822399566143147981263 2339733599349214721971895)
    ·
      refine ⟨3509600399023822082957843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2339733599349214721971895 3509600399023822082957843)
      ·
        refine ⟨5264400598535733124436765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3509600399023822082957843 5264400598535733124436765)
        ·
          refine ⟨1974150224450899921663787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5264400598535733124436765 1974150224450899921663787)
          ·
            refine ⟨2961225336676349882495681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1974150224450899921663787 2961225336676349882495681)
            ·
              refine ⟨2220919002507262411871761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2961225336676349882495681 2220919002507262411871761)
              ·
                refine ⟨1665689251880446808903821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2220919002507262411871761 1665689251880446808903821)
                ·
                  refine ⟨624633469455167553338933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1665689251880446808903821 624633469455167553338933)
                  ·
                    refine ⟨58559387761421958125525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 624633469455167553338933 58559387761421958125525)
                    ·
                      rfl

theorem cell22_171066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 2, 3, 5].length) (baseStart_171066 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_171066 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_171066 prefixEnd_171066 := by exact prefixLift 171066
  have htrace : WordTrace (prefixWord ++ tailWord_171066) baseStart_171066 baseEnd_171066 := by
    simpa [prefixWord, tailWord_171066, baseEnd_171066] using wordTrace_append hprefix tailTrace_171066
  have hstable : (prefixWord ++ tailWord_171066).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171066).length < 2 ^ (prefixWord ++ tailWord_171066).sum := by decide
  have hdescent : baseEnd_171066 < baseStart_171066 := by decide
  rcases family_descends (prefixWord ++ tailWord_171066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171068 : List Nat := [2, 2, 2, 2, 2, 3, 2, 1, 6]
def baseStart_171068 : Nat := 118140960795 + 171068 * 2 ^ 59
def prefixEnd_171068 : Nat := 4983230072969 + 3 ^ 40 * 171068 * 2
def baseEnd_171068 : Nat := 19520024134098206525173

theorem tailTrace_171068 : CollatzResearch.WordTrace tailWord_171068 prefixEnd_171068 19520024134098206525173 := by
  unfold tailWord_171068
  simp only [CollatzResearch.WordTrace]
  refine ⟨3119681272128663466748929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4159575029504884622331905 3119681272128663466748929)
  ·
    refine ⟨2339760954096497600061697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3119681272128663466748929 2339760954096497600061697)
    ·
      refine ⟨1754820715572373200046273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2339760954096497600061697 1754820715572373200046273)
      ·
        refine ⟨1316115536679279900034705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1754820715572373200046273 1316115536679279900034705)
        ·
          refine ⟨987086652509459925026029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1316115536679279900034705 987086652509459925026029)
          ·
            refine ⟨370157494691047471884761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 987086652509459925026029 370157494691047471884761)
            ·
              refine ⟨277618121018285603913571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 370157494691047471884761 277618121018285603913571)
              ·
                refine ⟨416427181527428405870357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 277618121018285603913571 416427181527428405870357)
                ·
                  refine ⟨19520024134098206525173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 416427181527428405870357 19520024134098206525173)
                  ·
                    rfl

theorem cell22_171068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 2, 1, 6].length) (baseStart_171068 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_171068 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_171068 prefixEnd_171068 := by exact prefixLift 171068
  have htrace : WordTrace (prefixWord ++ tailWord_171068) baseStart_171068 baseEnd_171068 := by
    simpa [prefixWord, tailWord_171068, baseEnd_171068] using wordTrace_append hprefix tailTrace_171068
  have hstable : (prefixWord ++ tailWord_171068).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171068).length < 2 ^ (prefixWord ++ tailWord_171068).sum := by decide
  have hdescent : baseEnd_171068 < baseStart_171068 := by decide
  rcases family_descends (prefixWord ++ tailWord_171068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171081 : List Nat := [1, 2, 1, 1, 2, 2, 2, 1, 6, 4]
def baseStart_171081 : Nat := 118140960795 + 171081 * 2 ^ 59
def prefixEnd_171081 : Nat := 4983230072969 + 3 ^ 40 * 171081 * 2
def baseEnd_171081 : Nat := 58564522567966919000479

theorem tailTrace_171081 : CollatzResearch.WordTrace tailWord_171081 prefixEnd_171081 58564522567966919000479 := by
  unfold tailWord_171081
  simp only [CollatzResearch.WordTrace]
  refine ⟨6239836693210230153721097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4159891128806820102480731 6239836693210230153721097)
  ·
    refine ⟨4679877519907672615290823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6239836693210230153721097 4679877519907672615290823)
    ·
      refine ⟨7019816279861508922936235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4679877519907672615290823 7019816279861508922936235)
      ·
        refine ⟨10529724419792263384404353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7019816279861508922936235 10529724419792263384404353)
        ·
          refine ⟨7897293314844197538303265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10529724419792263384404353 7897293314844197538303265)
          ·
            refine ⟨5922969986133148153727449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7897293314844197538303265 5922969986133148153727449)
            ·
              refine ⟨4442227489599861115295587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5922969986133148153727449 4442227489599861115295587)
              ·
                refine ⟨6663341234399791672943381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4442227489599861115295587 6663341234399791672943381)
                ·
                  refine ⟨312344120362490234669221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6663341234399791672943381 312344120362490234669221)
                  ·
                    refine ⟨58564522567966919000479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 312344120362490234669221 58564522567966919000479)
                    ·
                      rfl

theorem cell22_171081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 1, 6, 4].length) (baseStart_171081 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_171081 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_171081 prefixEnd_171081 := by exact prefixLift 171081
  have htrace : WordTrace (prefixWord ++ tailWord_171081) baseStart_171081 baseEnd_171081 := by
    simpa [prefixWord, tailWord_171081, baseEnd_171081] using wordTrace_append hprefix tailTrace_171081
  have hstable : (prefixWord ++ tailWord_171081).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171081).length < 2 ^ (prefixWord ++ tailWord_171081).sum := by decide
  have hdescent : baseEnd_171081 < baseStart_171081 := by decide
  rcases family_descends (prefixWord ++ tailWord_171081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171096 : List Nat := [2, 1, 2, 2, 1, 3, 3, 8]
def baseStart_171096 : Nat := 118140960795 + 171096 * 2 ^ 59
def prefixEnd_171096 : Nat := 4983230072969 + 3 ^ 40 * 171096 * 2
def baseEnd_171096 : Nat := 6507739708279097763937

theorem tailTrace_171096 : CollatzResearch.WordTrace tailWord_171096 prefixEnd_171096 6507739708279097763937 := by
  unfold tailWord_171096
  simp only [CollatzResearch.WordTrace]
  refine ⟨3120191894077943857758571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4160255858770591810344761 3120191894077943857758571)
  ·
    refine ⟨4680287841116915786637857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3120191894077943857758571 4680287841116915786637857)
    ·
      refine ⟨3510215880837686839978393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4680287841116915786637857 3510215880837686839978393)
      ·
        refine ⟨2632661910628265129983795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3510215880837686839978393 2632661910628265129983795)
        ·
          refine ⟨3948992865942397694975693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2632661910628265129983795 3948992865942397694975693)
          ·
            refine ⟨1480872324728399135615885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3948992865942397694975693 1480872324728399135615885)
            ·
              refine ⟨555327121773149675855957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1480872324728399135615885 555327121773149675855957)
              ·
                refine ⟨6507739708279097763937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 555327121773149675855957 6507739708279097763937)
                ·
                  rfl

theorem cell22_171096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 3, 8].length) (baseStart_171096 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_171096 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_171096 prefixEnd_171096 := by exact prefixLift 171096
  have htrace : WordTrace (prefixWord ++ tailWord_171096) baseStart_171096 baseEnd_171096 := by
    simpa [prefixWord, tailWord_171096, baseEnd_171096] using wordTrace_append hprefix tailTrace_171096
  have hstable : (prefixWord ++ tailWord_171096).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171096).length < 2 ^ (prefixWord ++ tailWord_171096).sum := by decide
  have hdescent : baseEnd_171096 < baseStart_171096 := by decide
  rcases family_descends (prefixWord ++ tailWord_171096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171175 : List Nat := [1, 1, 6, 2, 1, 1, 1, 4, 5]
def baseStart_171175 : Nat := 118140960795 + 171175 * 2 ^ 59
def prefixEnd_171175 : Nat := 4983230072969 + 3 ^ 40 * 171175 * 2
def baseEnd_171175 : Nat := 19532233562994002383397

theorem tailTrace_171175 : CollatzResearch.WordTrace tailWord_171175 prefixEnd_171175 19532233562994002383397 := by
  unfold tailWord_171175
  simp only [CollatzResearch.WordTrace]
  refine ⟨6243265154869684207642979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4162176769913122805095319 6243265154869684207642979)
  ·
    refine ⟨9364897732304526311464469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6243265154869684207642979 9364897732304526311464469)
    ·
      refine ⟨438979581201774670849897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 9364897732304526311464469 438979581201774670849897)
      ·
        refine ⟨329234685901331003137423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 438979581201774670849897 329234685901331003137423)
        ·
          refine ⟨493852028851996504706135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 329234685901331003137423 493852028851996504706135)
          ·
            refine ⟨740778043277994757059203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 493852028851996504706135 740778043277994757059203)
            ·
              refine ⟨1111167064916992135588805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 740778043277994757059203 1111167064916992135588805)
              ·
                refine ⟨208343824671936025422901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1111167064916992135588805 208343824671936025422901)
                ·
                  refine ⟨19532233562994002383397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 208343824671936025422901 19532233562994002383397)
                  ·
                    rfl

theorem cell22_171175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 4, 5].length) (baseStart_171175 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_171175 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_171175 prefixEnd_171175 := by exact prefixLift 171175
  have htrace : WordTrace (prefixWord ++ tailWord_171175) baseStart_171175 baseEnd_171175 := by
    simpa [prefixWord, tailWord_171175, baseEnd_171175] using wordTrace_append hprefix tailTrace_171175
  have hstable : (prefixWord ++ tailWord_171175).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171175).length < 2 ^ (prefixWord ++ tailWord_171175).sum := by decide
  have hdescent : baseEnd_171175 < baseStart_171175 := by decide
  rcases family_descends (prefixWord ++ tailWord_171175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171213 : List Nat := [1, 6, 2, 2, 1, 1, 2, 3, 1, 3]
def baseStart_171213 : Nat := 118140960795 + 171213 * 2 ^ 59
def prefixEnd_171213 : Nat := 4983230072969 + 3 ^ 40 * 171213 * 2
def baseEnd_171213 : Nat := 58609708865562574700075

theorem tailTrace_171213 : CollatzResearch.WordTrace tailWord_171213 prefixEnd_171213 58609708865562574700075 := by
  unfold tailWord_171213
  simp only [CollatzResearch.WordTrace]
  refine ⟨6244651128732016697526293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4163100752488011131684195 6244651128732016697526293)
  ·
    refine ⟨292718021659313282696545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 6244651128732016697526293 292718021659313282696545)
    ·
      refine ⟨219538516244484962022409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 292718021659313282696545 219538516244484962022409)
      ·
        refine ⟨164653887183363721516807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 219538516244484962022409 164653887183363721516807)
        ·
          refine ⟨246980830775045582275211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164653887183363721516807 246980830775045582275211)
          ·
            refine ⟨370471246162568373412817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 246980830775045582275211 370471246162568373412817)
            ·
              refine ⟨277853434621926280059613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 370471246162568373412817 277853434621926280059613)
              ·
                refine ⟨104195037983222355022355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 277853434621926280059613 104195037983222355022355)
                ·
                  refine ⟨156292556974833532533533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 104195037983222355022355 156292556974833532533533)
                  ·
                    refine ⟨58609708865562574700075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 156292556974833532533533 58609708865562574700075)
                    ·
                      rfl

theorem cell22_171213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 2, 3, 1, 3].length) (baseStart_171213 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_171213 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_171213 prefixEnd_171213 := by exact prefixLift 171213
  have htrace : WordTrace (prefixWord ++ tailWord_171213) baseStart_171213 baseEnd_171213 := by
    simpa [prefixWord, tailWord_171213, baseEnd_171213] using wordTrace_append hprefix tailTrace_171213
  have hstable : (prefixWord ++ tailWord_171213).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171213).length < 2 ^ (prefixWord ++ tailWord_171213).sum := by decide
  have hdescent : baseEnd_171213 < baseStart_171213 := by decide
  rcases family_descends (prefixWord ++ tailWord_171213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171265 : List Nat := [1, 2, 4, 1, 1, 3, 4, 6]
def baseStart_171265 : Nat := 118140960795 + 171265 * 2 ^ 59
def prefixEnd_171265 : Nat := 4983230072969 + 3 ^ 40 * 171265 * 2
def baseEnd_171265 : Nat := 6514167725361308044435

theorem tailTrace_171265 : CollatzResearch.WordTrace tailWord_171265 prefixEnd_171265 6514167725361308044435 := by
  unfold tailWord_171265
  simp only [CollatzResearch.WordTrace]
  refine ⟨6246547724543629578419249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4164365149695753052279499 6246547724543629578419249)
  ·
    refine ⟨4684910793407722183814437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6246547724543629578419249 4684910793407722183814437)
    ·
      refine ⟨878420773763947909465207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4684910793407722183814437 878420773763947909465207)
      ·
        refine ⟨1317631160645921864197811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 878420773763947909465207 1317631160645921864197811)
        ·
          refine ⟨1976446740968882796296717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1317631160645921864197811 1976446740968882796296717)
          ·
            refine ⟨741167527863331048611269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1976446740968882796296717 741167527863331048611269)
            ·
              refine ⟨138968911474374571614613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 741167527863331048611269 138968911474374571614613)
              ·
                refine ⟨6514167725361308044435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 138968911474374571614613 6514167725361308044435)
                ·
                  rfl

theorem cell22_171265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 4, 6].length) (baseStart_171265 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_171265 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_171265 prefixEnd_171265 := by exact prefixLift 171265
  have htrace : WordTrace (prefixWord ++ tailWord_171265) baseStart_171265 baseEnd_171265 := by
    simpa [prefixWord, tailWord_171265, baseEnd_171265] using wordTrace_append hprefix tailTrace_171265
  have hstable : (prefixWord ++ tailWord_171265).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171265).length < 2 ^ (prefixWord ++ tailWord_171265).sum := by decide
  have hdescent : baseEnd_171265 < baseStart_171265 := by decide
  rcases family_descends (prefixWord ++ tailWord_171265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171308 : List Nat := [2, 2, 1, 1, 1, 3, 1, 3, 1, 7]
def baseStart_171308 : Nat := 118140960795 + 171308 * 2 ^ 59
def prefixEnd_171308 : Nat := 4983230072969 + 3 ^ 40 * 171308 * 2
def baseEnd_171308 : Nat := 58642229307013993574783

theorem tailTrace_171308 : CollatzResearch.WordTrace tailWord_171308 prefixEnd_171308 58642229307013993574783 := by
  unfold tailWord_171308
  simp only [CollatzResearch.WordTrace]
  refine ⟨3124058031693923961117289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4165410708925231948156385 3124058031693923961117289)
  ·
    refine ⟨2343043523770442970837967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3124058031693923961117289 2343043523770442970837967)
    ·
      refine ⟨3514565285655664456256951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2343043523770442970837967 3514565285655664456256951)
      ·
        refine ⟨5271847928483496684385427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3514565285655664456256951 5271847928483496684385427)
        ·
          refine ⟨7907771892725245026578141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5271847928483496684385427 7907771892725245026578141)
          ·
            refine ⟨2965414459771966884966803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7907771892725245026578141 2965414459771966884966803)
            ·
              refine ⟨4448121689657950327450205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2965414459771966884966803 4448121689657950327450205)
              ·
                refine ⟨1668045633621731372793827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4448121689657950327450205 1668045633621731372793827)
                ·
                  refine ⟨2502068450432597059190741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1668045633621731372793827 2502068450432597059190741)
                  ·
                    refine ⟨58642229307013993574783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2502068450432597059190741 58642229307013993574783)
                    ·
                      rfl

theorem cell22_171308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 7].length) (baseStart_171308 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_171308 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_171308 prefixEnd_171308 := by exact prefixLift 171308
  have htrace : WordTrace (prefixWord ++ tailWord_171308) baseStart_171308 baseEnd_171308 := by
    simpa [prefixWord, tailWord_171308, baseEnd_171308] using wordTrace_append hprefix tailTrace_171308
  have hstable : (prefixWord ++ tailWord_171308).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171308).length < 2 ^ (prefixWord ++ tailWord_171308).sum := by decide
  have hdescent : baseEnd_171308 < baseStart_171308 := by decide
  rcases family_descends (prefixWord ++ tailWord_171308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171400 : List Nat := [2, 1, 3, 3, 1, 3, 9]
def baseStart_171400 : Nat := 118140960795 + 171400 * 2 ^ 59
def prefixEnd_171400 : Nat := 4983230072969 + 3 ^ 40 * 171400 * 2
def baseEnd_171400 : Nat := 2173100843968756306463

theorem tailTrace_171400 : CollatzResearch.WordTrace tailWord_171400 prefixEnd_171400 2173100843968756306463 := by
  unfold tailWord_171400
  simp only [CollatzResearch.WordTrace]
  refine ⟨3125735789527273817291827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4167647719369698423055769 3125735789527273817291827)
  ·
    refine ⟨4688603684290910725937741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3125735789527273817291827 4688603684290910725937741)
    ·
      refine ⟨1758226381609091522226653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4688603684290910725937741 1758226381609091522226653)
      ·
        refine ⟨659334893103409320834995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1758226381609091522226653 659334893103409320834995)
        ·
          refine ⟨989002339655113981252493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 659334893103409320834995 989002339655113981252493)
          ·
            refine ⟨370875877370667742969685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 989002339655113981252493 370875877370667742969685)
            ·
              refine ⟨2173100843968756306463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 370875877370667742969685 2173100843968756306463)
              ·
                rfl

theorem cell22_171400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 9].length) (baseStart_171400 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_171400 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_171400 prefixEnd_171400 := by exact prefixLift 171400
  have htrace : WordTrace (prefixWord ++ tailWord_171400) baseStart_171400 baseEnd_171400 := by
    simpa [prefixWord, tailWord_171400, baseEnd_171400] using wordTrace_append hprefix tailTrace_171400
  have hstable : (prefixWord ++ tailWord_171400).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171400).length < 2 ^ (prefixWord ++ tailWord_171400).sum := by decide
  have hdescent : baseEnd_171400 < baseStart_171400 := by decide
  rcases family_descends (prefixWord ++ tailWord_171400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171421 : List Nat := [1, 4, 2, 1, 3, 2, 3, 1, 2, 3]
def baseStart_171421 : Nat := 118140960795 + 171421 * 2 ^ 59
def prefixEnd_171421 : Nat := 4983230072969 + 3 ^ 40 * 171421 * 2
def baseEnd_171421 : Nat := 58680911516319365499437

theorem tailTrace_171421 : CollatzResearch.WordTrace tailWord_171421 prefixEnd_171421 58680911516319365499437 := by
  unfold tailWord_171421
  simp only [CollatzResearch.WordTrace]
  refine ⟨6252237511978468221098117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4168158341318978814065411 6252237511978468221098117)
  ·
    refine ⟨1172294533495962791455897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6252237511978468221098117 1172294533495962791455897)
    ·
      refine ⟨879220900121972093591923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1172294533495962791455897 879220900121972093591923)
      ·
        refine ⟨1318831350182958140387885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 879220900121972093591923 1318831350182958140387885)
        ·
          refine ⟨494561756318609302645457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1318831350182958140387885 494561756318609302645457)
          ·
            refine ⟨370921317238956976984093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 494561756318609302645457 370921317238956976984093)
            ·
              refine ⟨139095493964608866369035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 370921317238956976984093 139095493964608866369035)
              ·
                refine ⟨208643240946913299553553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 139095493964608866369035 208643240946913299553553)
                ·
                  refine ⟨156482430710184974665165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 208643240946913299553553 156482430710184974665165)
                  ·
                    refine ⟨58680911516319365499437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 156482430710184974665165 58680911516319365499437)
                    ·
                      rfl

theorem cell22_171421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 3, 1, 2, 3].length) (baseStart_171421 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_171421 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_171421 prefixEnd_171421 := by exact prefixLift 171421
  have htrace : WordTrace (prefixWord ++ tailWord_171421) baseStart_171421 baseEnd_171421 := by
    simpa [prefixWord, tailWord_171421, baseEnd_171421] using wordTrace_append hprefix tailTrace_171421
  have hstable : (prefixWord ++ tailWord_171421).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171421).length < 2 ^ (prefixWord ++ tailWord_171421).sum := by decide
  have hdescent : baseEnd_171421 < baseStart_171421 := by decide
  rcases family_descends (prefixWord ++ tailWord_171421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171539 : List Nat := [1, 1, 1, 2, 1, 6, 2, 3, 2, 3]
def baseStart_171539 : Nat := 118140960795 + 171539 * 2 ^ 59
def prefixEnd_171539 : Nat := 4983230072969 + 3 ^ 40 * 171539 * 2
def baseEnd_171539 : Nat := 58721305327806391049075

theorem tailTrace_171539 : CollatzResearch.WordTrace tailWord_171539 prefixEnd_171539 58721305327806391049075 := by
  unfold tailWord_171539
  simp only [CollatzResearch.WordTrace]
  refine ⟨6256541325550974373893671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4171027550367316249262447 6256541325550974373893671)
  ·
    refine ⟨9384811988326461560840507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6256541325550974373893671 9384811988326461560840507)
    ·
      refine ⟨14077217982489692341260761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9384811988326461560840507 14077217982489692341260761)
      ·
        refine ⟨10557913486867269255945571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14077217982489692341260761 10557913486867269255945571)
        ·
          refine ⟨15836870230300903883918357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10557913486867269255945571 15836870230300903883918357)
          ·
            refine ⟨742353292045354869558673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 15836870230300903883918357 742353292045354869558673)
            ·
              refine ⟨556764969034016152169005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 742353292045354869558673 556764969034016152169005)
              ·
                refine ⟨208786863387756057063377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 556764969034016152169005 208786863387756057063377)
                ·
                  refine ⟨156590147540817042797533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 208786863387756057063377 156590147540817042797533)
                  ·
                    refine ⟨58721305327806391049075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 156590147540817042797533 58721305327806391049075)
                    ·
                      rfl

theorem cell22_171539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 2, 3, 2, 3].length) (baseStart_171539 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_171539 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_171539 prefixEnd_171539 := by exact prefixLift 171539
  have htrace : WordTrace (prefixWord ++ tailWord_171539) baseStart_171539 baseEnd_171539 := by
    simpa [prefixWord, tailWord_171539, baseEnd_171539] using wordTrace_append hprefix tailTrace_171539
  have hstable : (prefixWord ++ tailWord_171539).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171539).length < 2 ^ (prefixWord ++ tailWord_171539).sum := by decide
  have hdescent : baseEnd_171539 < baseStart_171539 := by decide
  rcases family_descends (prefixWord ++ tailWord_171539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171554 : List Nat := [3, 3, 1, 1, 1, 1, 5, 1, 2, 4]
def baseStart_171554 : Nat := 118140960795 + 171554 * 2 ^ 59
def prefixEnd_171554 : Nat := 4983230072969 + 3 ^ 40 * 171554 * 2
def baseEnd_171554 : Nat := 58726440134351351924029

theorem tailTrace_171554 : CollatzResearch.WordTrace tailWord_171554 prefixEnd_171554 58726440134351351924029 := by
  unfold tailWord_171554
  simp only [CollatzResearch.WordTrace]
  refine ⟨1564272105124157983922429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4171392280331087957126477 1564272105124157983922429)
  ·
    refine ⟨586602039421559243970911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1564272105124157983922429 586602039421559243970911)
    ·
      refine ⟨879903059132338865956367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 586602039421559243970911 879903059132338865956367)
      ·
        refine ⟨1319854588698508298934551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 879903059132338865956367 1319854588698508298934551)
        ·
          refine ⟨1979781883047762448401827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1319854588698508298934551 1979781883047762448401827)
          ·
            refine ⟨2969672824571643672602741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1979781883047762448401827 2969672824571643672602741)
            ·
              refine ⟨278406827303591594306507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2969672824571643672602741 278406827303591594306507)
              ·
                refine ⟨417610240955387391459761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 278406827303591594306507 417610240955387391459761)
                ·
                  refine ⟨313207680716540543594821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 417610240955387391459761 313207680716540543594821)
                  ·
                    refine ⟨58726440134351351924029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 313207680716540543594821 58726440134351351924029)
                    ·
                      rfl

theorem cell22_171554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 5, 1, 2, 4].length) (baseStart_171554 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_171554 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_171554 prefixEnd_171554 := by exact prefixLift 171554
  have htrace : WordTrace (prefixWord ++ tailWord_171554) baseStart_171554 baseEnd_171554 := by
    simpa [prefixWord, tailWord_171554, baseEnd_171554] using wordTrace_append hprefix tailTrace_171554
  have hstable : (prefixWord ++ tailWord_171554).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171554).length < 2 ^ (prefixWord ++ tailWord_171554).sum := by decide
  have hdescent : baseEnd_171554 < baseStart_171554 := by decide
  rcases family_descends (prefixWord ++ tailWord_171554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171560 : List Nat := [2, 1, 5, 2, 3, 1, 2, 1, 1, 4]
def baseStart_171560 : Nat := 118140960795 + 171560 * 2 ^ 59
def prefixEnd_171560 : Nat := 4983230072969 + 3 ^ 40 * 171560 * 2
def baseEnd_171560 : Nat := 58728494056969336274011

theorem tailTrace_171560 : CollatzResearch.WordTrace tailWord_171560 prefixEnd_171560 58728494056969336274011 := by
  unfold tailWord_171560
  simp only [CollatzResearch.WordTrace]
  refine ⟨3128653629237447480204067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4171538172316596640272089 3128653629237447480204067)
  ·
    refine ⟨4692980443856171220306101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3128653629237447480204067 4692980443856171220306101)
    ·
      refine ⟨439966916611516051903697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4692980443856171220306101 439966916611516051903697)
      ·
        refine ⟨329975187458637038927773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 439966916611516051903697 329975187458637038927773)
        ·
          refine ⟨123740695296988889597915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 329975187458637038927773 123740695296988889597915)
          ·
            refine ⟨185611042945483334396873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123740695296988889597915 185611042945483334396873)
            ·
              refine ⟨139208282209112500797655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 185611042945483334396873 139208282209112500797655)
              ·
                refine ⟨208812423313668751196483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 139208282209112500797655 208812423313668751196483)
                ·
                  refine ⟨313218634970503126794725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 208812423313668751196483 313218634970503126794725)
                  ·
                    refine ⟨58728494056969336274011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 313218634970503126794725 58728494056969336274011)
                    ·
                      rfl

theorem cell22_171560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 2, 1, 1, 4].length) (baseStart_171560 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_171560 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_171560 prefixEnd_171560 := by exact prefixLift 171560
  have htrace : WordTrace (prefixWord ++ tailWord_171560) baseStart_171560 baseEnd_171560 := by
    simpa [prefixWord, tailWord_171560, baseEnd_171560] using wordTrace_append hprefix tailTrace_171560
  have hstable : (prefixWord ++ tailWord_171560).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171560).length < 2 ^ (prefixWord ++ tailWord_171560).sum := by decide
  have hdescent : baseEnd_171560 < baseStart_171560 := by decide
  rcases family_descends (prefixWord ++ tailWord_171560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171590 : List Nat := [6, 1, 1, 1, 4, 1, 1, 1, 1, 5]
def baseStart_171590 : Nat := 118140960795 + 171590 * 2 ^ 59
def prefixEnd_171590 : Nat := 4983230072969 + 3 ^ 40 * 171590 * 2
def baseEnd_171590 : Nat := 58738763670059258023919

theorem tailTrace_171590 : CollatzResearch.WordTrace tailWord_171590 prefixEnd_171590 58738763670059258023919 := by
  unfold tailWord_171590
  simp only [CollatzResearch.WordTrace]
  refine ⟨195575045261444065125007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 4172267632244140056000149 195575045261444065125007)
  ·
    refine ⟨293362567892166097687511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195575045261444065125007 293362567892166097687511)
    ·
      refine ⟨440043851838249146531267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 293362567892166097687511 440043851838249146531267)
      ·
        refine ⟨660065777757373719796901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 440043851838249146531267 660065777757373719796901)
        ·
          refine ⟨123762333329507572461919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 660065777757373719796901 123762333329507572461919)
          ·
            refine ⟨185643499994261358692879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123762333329507572461919 185643499994261358692879)
            ·
              refine ⟨278465249991392038039319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 185643499994261358692879 278465249991392038039319)
              ·
                refine ⟨417697874987088057058979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 278465249991392038039319 417697874987088057058979)
                ·
                  refine ⟨626546812480632085588469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 417697874987088057058979 626546812480632085588469)
                  ·
                    refine ⟨58738763670059258023919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 626546812480632085588469 58738763670059258023919)
                    ·
                      rfl

theorem cell22_171590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 1, 1, 1, 5].length) (baseStart_171590 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_171590 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_171590 prefixEnd_171590 := by exact prefixLift 171590
  have htrace : WordTrace (prefixWord ++ tailWord_171590) baseStart_171590 baseEnd_171590 := by
    simpa [prefixWord, tailWord_171590, baseEnd_171590] using wordTrace_append hprefix tailTrace_171590
  have hstable : (prefixWord ++ tailWord_171590).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171590).length < 2 ^ (prefixWord ++ tailWord_171590).sum := by decide
  have hdescent : baseEnd_171590 < baseStart_171590 := by decide
  rcases family_descends (prefixWord ++ tailWord_171590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171642 : List Nat := [3, 1, 1, 1, 1, 1, 1, 7, 6]
def baseStart_171642 : Nat := 118140960795 + 171642 * 2 ^ 59
def prefixEnd_171642 : Nat := 4983230072969 + 3 ^ 40 * 171642 * 2
def baseEnd_171642 : Nat := 19585521444249485241253

theorem tailTrace_171642 : CollatzResearch.WordTrace tailWord_171642 prefixEnd_171642 19585521444249485241253 := by
  unfold tailWord_171642
  simp only [CollatzResearch.WordTrace]
  refine ⟨1565074511044455741223295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4173532029451881976595453 1565074511044455741223295)
  ·
    refine ⟨2347611766566683611834943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1565074511044455741223295 2347611766566683611834943)
    ·
      refine ⟨3521417649850025417752415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2347611766566683611834943 3521417649850025417752415)
      ·
        refine ⟨5282126474775038126628623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3521417649850025417752415 5282126474775038126628623)
        ·
          refine ⟨7923189712162557189942935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5282126474775038126628623 7923189712162557189942935)
          ·
            refine ⟨11884784568243835784914403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7923189712162557189942935 11884784568243835784914403)
            ·
              refine ⟨17827176852365753677371605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11884784568243835784914403 17827176852365753677371605)
              ·
                refine ⟨417824457477322351813397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 17827176852365753677371605 417824457477322351813397)
                ·
                  refine ⟨19585521444249485241253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 417824457477322351813397 19585521444249485241253)
                  ·
                    rfl

theorem cell22_171642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 7, 6].length) (baseStart_171642 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_171642 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_171642 prefixEnd_171642 := by exact prefixLift 171642
  have htrace : WordTrace (prefixWord ++ tailWord_171642) baseStart_171642 baseEnd_171642 := by
    simpa [prefixWord, tailWord_171642, baseEnd_171642] using wordTrace_append hprefix tailTrace_171642
  have hstable : (prefixWord ++ tailWord_171642).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171642).length < 2 ^ (prefixWord ++ tailWord_171642).sum := by decide
  have hdescent : baseEnd_171642 < baseStart_171642 := by decide
  rcases family_descends (prefixWord ++ tailWord_171642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171687 : List Nat := [1, 1, 6, 14]
def baseStart_171687 : Nat := 118140960795 + 171687 * 2 ^ 59
def prefixEnd_171687 : Nat := 4983230072969 + 3 ^ 40 * 171687 * 2
def baseEnd_171687 : Nat := 80619984571170560149

theorem tailTrace_171687 : CollatzResearch.WordTrace tailWord_171687 prefixEnd_171687 80619984571170560149 := by
  unfold tailWord_171687
  simp only [CollatzResearch.WordTrace]
  refine ⟨6261939329014795650281315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4174626219343197100187543 6261939329014795650281315)
  ·
    refine ⟨9392908993522193475421973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6261939329014795650281315 9392908993522193475421973)
    ·
      refine ⟨440292609071352819160405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 9392908993522193475421973 440292609071352819160405)
      ·
        refine ⟨80619984571170560149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 14 440292609071352819160405 80619984571170560149)
        ·
          rfl

theorem cell22_171687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 14].length) (baseStart_171687 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_171687 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_171687 prefixEnd_171687 := by exact prefixLift 171687
  have htrace : WordTrace (prefixWord ++ tailWord_171687) baseStart_171687 baseEnd_171687 := by
    simpa [prefixWord, tailWord_171687, baseEnd_171687] using wordTrace_append hprefix tailTrace_171687
  have hstable : (prefixWord ++ tailWord_171687).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171687).length < 2 ^ (prefixWord ++ tailWord_171687).sum := by decide
  have hdescent : baseEnd_171687 < baseStart_171687 := by decide
  rcases family_descends (prefixWord ++ tailWord_171687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171749 : List Nat := [1, 3, 1, 4, 1, 1, 3, 1, 7]
def baseStart_171749 : Nat := 118140960795 + 171749 * 2 ^ 59
def prefixEnd_171749 : Nat := 4983230072969 + 3 ^ 40 * 171749 * 2
def baseEnd_171749 : Nat := 19597730873145281099477

theorem tailTrace_171749 : CollatzResearch.WordTrace tailWord_171749 prefixEnd_171749 19597730873145281099477 := by
  unfold tailWord_171749
  simp only [CollatzResearch.WordTrace]
  refine ⟨6264200654790180239038301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4176133769860120159358867 6264200654790180239038301)
  ·
    refine ⟨2349075245546317589639363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6264200654790180239038301 2349075245546317589639363)
    ·
      refine ⟨3523612868319476384459045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2349075245546317589639363 3523612868319476384459045)
      ·
        refine ⟨660677412809901822086071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3523612868319476384459045 660677412809901822086071)
        ·
          refine ⟨991016119214852733129107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 660677412809901822086071 991016119214852733129107)
          ·
            refine ⟨1486524178822279099693661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 991016119214852733129107 1486524178822279099693661)
            ·
              refine ⟨557446567058354662385123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1486524178822279099693661 557446567058354662385123)
              ·
                refine ⟨836169850587531993577685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 557446567058354662385123 836169850587531993577685)
                ·
                  refine ⟨19597730873145281099477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 836169850587531993577685 19597730873145281099477)
                  ·
                    rfl

theorem cell22_171749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 3, 1, 7].length) (baseStart_171749 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_171749 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_171749 prefixEnd_171749 := by exact prefixLift 171749
  have htrace : WordTrace (prefixWord ++ tailWord_171749) baseStart_171749 baseEnd_171749 := by
    simpa [prefixWord, tailWord_171749, baseEnd_171749] using wordTrace_append hprefix tailTrace_171749
  have hstable : (prefixWord ++ tailWord_171749).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171749).length < 2 ^ (prefixWord ++ tailWord_171749).sum := by decide
  have hdescent : baseEnd_171749 < baseStart_171749 := by decide
  rcases family_descends (prefixWord ++ tailWord_171749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171779 : List Nat := [1, 1, 1, 3, 2, 2, 2, 3, 3, 4]
def baseStart_171779 : Nat := 118140960795 + 171779 * 2 ^ 59
def prefixEnd_171779 : Nat := 4983230072969 + 3 ^ 40 * 171779 * 2
def baseEnd_171779 : Nat := 58803462232525765048339

theorem tailTrace_171779 : CollatzResearch.WordTrace tailWord_171779 prefixEnd_171779 58803462232525765048339 := by
  unfold tailWord_171779
  simp only [CollatzResearch.WordTrace]
  refine ⟨6265294844681495362630391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4176863229787663575086927 6265294844681495362630391)
  ·
    refine ⟨9397942267022243043945587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6265294844681495362630391 9397942267022243043945587)
    ·
      refine ⟨14096913400533364565918381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9397942267022243043945587 14096913400533364565918381)
      ·
        refine ⟨5286342525200011712219393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14096913400533364565918381 5286342525200011712219393)
        ·
          refine ⟨3964756893900008784164545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5286342525200011712219393 3964756893900008784164545)
          ·
            refine ⟨2973567670425006588123409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3964756893900008784164545 2973567670425006588123409)
            ·
              refine ⟨2230175752818754941092557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2973567670425006588123409 2230175752818754941092557)
              ·
                refine ⟨836315907307033102909709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2230175752818754941092557 836315907307033102909709)
                ·
                  refine ⟨313618465240137413591141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 836315907307033102909709 313618465240137413591141)
                  ·
                    refine ⟨58803462232525765048339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 313618465240137413591141 58803462232525765048339)
                    ·
                      rfl

theorem cell22_171779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 3, 3, 4].length) (baseStart_171779 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_171779 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_171779 prefixEnd_171779 := by exact prefixLift 171779
  have htrace : WordTrace (prefixWord ++ tailWord_171779) baseStart_171779 baseEnd_171779 := by
    simpa [prefixWord, tailWord_171779, baseEnd_171779] using wordTrace_append hprefix tailTrace_171779
  have hstable : (prefixWord ++ tailWord_171779).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171779).length < 2 ^ (prefixWord ++ tailWord_171779).sum := by decide
  have hdescent : baseEnd_171779 < baseStart_171779 := by decide
  rcases family_descends (prefixWord ++ tailWord_171779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171811 : List Nat := [1, 1, 1, 4, 2, 1, 2, 6, 4]
def baseStart_171811 : Nat := 118140960795 + 171811 * 2 ^ 59
def prefixEnd_171811 : Nat := 4983230072969 + 3 ^ 40 * 171811 * 2
def baseEnd_171811 : Nat := 19604805495496116082747

theorem tailTrace_171811 : CollatzResearch.WordTrace tailWord_171811 prefixEnd_171811 19604805495496116082747 := by
  unfold tailWord_171811
  simp only [CollatzResearch.WordTrace]
  refine ⟨6266461980565564827795287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4177641320377043218530191 6266461980565564827795287)
  ·
    refine ⟨9399692970848347241692931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6266461980565564827795287 9399692970848347241692931)
    ·
      refine ⟨14099539456272520862539397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9399692970848347241692931 14099539456272520862539397)
      ·
        refine ⟨2643663648051097661726137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14099539456272520862539397 2643663648051097661726137)
        ·
          refine ⟨1982747736038323246294603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2643663648051097661726137 1982747736038323246294603)
          ·
            refine ⟨2974121604057484869441905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1982747736038323246294603 2974121604057484869441905)
            ·
              refine ⟨2230591203043113652081429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2974121604057484869441905 2230591203043113652081429)
              ·
                refine ⟨104558962642645952441317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2230591203043113652081429 104558962642645952441317)
                ·
                  refine ⟨19604805495496116082747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 104558962642645952441317 19604805495496116082747)
                  ·
                    rfl

theorem cell22_171811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 6, 4].length) (baseStart_171811 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_171811 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_171811 prefixEnd_171811 := by exact prefixLift 171811
  have htrace : WordTrace (prefixWord ++ tailWord_171811) baseStart_171811 baseEnd_171811 := by
    simpa [prefixWord, tailWord_171811, baseEnd_171811] using wordTrace_append hprefix tailTrace_171811
  have hstable : (prefixWord ++ tailWord_171811).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171811).length < 2 ^ (prefixWord ++ tailWord_171811).sum := by decide
  have hdescent : baseEnd_171811 < baseStart_171811 := by decide
  rcases family_descends (prefixWord ++ tailWord_171811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171830 : List Nat := [5, 1, 2, 2, 1, 1, 3, 2, 1, 4]
def baseStart_171830 : Nat := 118140960795 + 171830 * 2 ^ 59
def prefixEnd_171830 : Nat := 4983230072969 + 3 ^ 40 * 171830 * 2
def baseEnd_171830 : Nat := 58820920574778632023183

theorem tailTrace_171830 : CollatzResearch.WordTrace tailWord_171830 prefixEnd_171830 58820920574778632023183 := by
  unfold tailWord_171830
  simp only [CollatzResearch.WordTrace]
  refine ⟨391697185468545692046059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4178103311664487381824629 391697185468545692046059)
  ·
    refine ⟨587545778202818538069089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 391697185468545692046059 587545778202818538069089)
    ·
      refine ⟨440659333652113903551817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 587545778202818538069089 440659333652113903551817)
      ·
        refine ⟨330494500239085427663863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 440659333652113903551817 330494500239085427663863)
        ·
          refine ⟨495741750358628141495795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 330494500239085427663863 495741750358628141495795)
          ·
            refine ⟨743612625537942212243693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 495741750358628141495795 743612625537942212243693)
            ·
              refine ⟨278854734576728329591385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 743612625537942212243693 278854734576728329591385)
              ·
                refine ⟨209141050932546247193539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 278854734576728329591385 209141050932546247193539)
                ·
                  refine ⟨313711576398819370790309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 209141050932546247193539 313711576398819370790309)
                  ·
                    refine ⟨58820920574778632023183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 313711576398819370790309 58820920574778632023183)
                    ·
                      rfl

theorem cell22_171830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 3, 2, 1, 4].length) (baseStart_171830 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_171830 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_171830 prefixEnd_171830 := by exact prefixLift 171830
  have htrace : WordTrace (prefixWord ++ tailWord_171830) baseStart_171830 baseEnd_171830 := by
    simpa [prefixWord, tailWord_171830, baseEnd_171830] using wordTrace_append hprefix tailTrace_171830
  have hstable : (prefixWord ++ tailWord_171830).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171830).length < 2 ^ (prefixWord ++ tailWord_171830).sum := by decide
  have hdescent : baseEnd_171830 < baseStart_171830 := by decide
  rcases family_descends (prefixWord ++ tailWord_171830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171860 : List Nat := [2, 4, 1, 1, 3, 2, 2, 2, 2, 3]
def baseStart_171860 : Nat := 118140960795 + 171860 * 2 ^ 59
def prefixEnd_171860 : Nat := 4983230072969 + 3 ^ 40 * 171860 * 2
def baseEnd_171860 : Nat := 58831190187868553773091

theorem tailTrace_171860 : CollatzResearch.WordTrace tailWord_171860 prefixEnd_171860 58831190187868553773091 := by
  unfold tailWord_171860
  simp only [CollatzResearch.WordTrace]
  refine ⟨3134124578694023098164517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4178832771592030797552689 3134124578694023098164517)
  ·
    refine ⟨587648358505129330905847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3134124578694023098164517 587648358505129330905847)
    ·
      refine ⟨881472537757693996358771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 587648358505129330905847 881472537757693996358771)
      ·
        refine ⟨1322208806636540994538157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 881472537757693996358771 1322208806636540994538157)
        ·
          refine ⟨495828302488702872951809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1322208806636540994538157 495828302488702872951809)
          ·
            refine ⟨371871226866527154713857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 495828302488702872951809 371871226866527154713857)
            ·
              refine ⟨278903420149895366035393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 371871226866527154713857 278903420149895366035393)
              ·
                refine ⟨209177565112421524526545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 278903420149895366035393 209177565112421524526545)
                ·
                  refine ⟨156883173834316143394909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 209177565112421524526545 156883173834316143394909)
                  ·
                    refine ⟨58831190187868553773091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 156883173834316143394909 58831190187868553773091)
                    ·
                      rfl

theorem cell22_171860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 2, 2, 2, 3].length) (baseStart_171860 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_171860 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_171860 prefixEnd_171860 := by exact prefixLift 171860
  have htrace : WordTrace (prefixWord ++ tailWord_171860) baseStart_171860 baseEnd_171860 := by
    simpa [prefixWord, tailWord_171860, baseEnd_171860] using wordTrace_append hprefix tailTrace_171860
  have hstable : (prefixWord ++ tailWord_171860).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171860).length < 2 ^ (prefixWord ++ tailWord_171860).sum := by decide
  have hdescent : baseEnd_171860 < baseStart_171860 := by decide
  rcases family_descends (prefixWord ++ tailWord_171860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171899 : List Nat := [1, 1, 1, 1, 1, 5, 1, 1, 3, 7]
def baseStart_171899 : Nat := 118140960795 + 171899 * 2 ^ 59
def prefixEnd_171899 : Nat := 4983230072969 + 3 ^ 40 * 171899 * 2
def baseEnd_171899 : Nat := 58844540684885452047971

theorem tailTrace_171899 : CollatzResearch.WordTrace tailWord_171899 prefixEnd_171899 58844540684885452047971 := by
  unfold tailWord_171899
  simp only [CollatzResearch.WordTrace]
  refine ⟨6269671604246755856998751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4179781069497837237999167 6269671604246755856998751)
  ·
    refine ⟨9404507406370133785498127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6269671604246755856998751 9404507406370133785498127)
    ·
      refine ⟨14106761109555200678247191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9404507406370133785498127 14106761109555200678247191)
      ·
        refine ⟨21160141664332801017370787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14106761109555200678247191 21160141664332801017370787)
        ·
          refine ⟨31740212496499201526056181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21160141664332801017370787 31740212496499201526056181)
          ·
            refine ⟨2975644921546800143067767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 31740212496499201526056181 2975644921546800143067767)
            ·
              refine ⟨4463467382320200214601651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2975644921546800143067767 4463467382320200214601651)
              ·
                refine ⟨6695201073480300321902477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4463467382320200214601651 6695201073480300321902477)
                ·
                  refine ⟨2510700402555112620713429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6695201073480300321902477 2510700402555112620713429)
                  ·
                    refine ⟨58844540684885452047971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2510700402555112620713429 58844540684885452047971)
                    ·
                      rfl

theorem cell22_171899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 1, 3, 7].length) (baseStart_171899 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_171899 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_171899 prefixEnd_171899 := by exact prefixLift 171899
  have htrace : WordTrace (prefixWord ++ tailWord_171899) baseStart_171899 baseEnd_171899 := by
    simpa [prefixWord, tailWord_171899, baseEnd_171899] using wordTrace_append hprefix tailTrace_171899
  have hstable : (prefixWord ++ tailWord_171899).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171899).length < 2 ^ (prefixWord ++ tailWord_171899).sum := by decide
  have hdescent : baseEnd_171899 < baseStart_171899 := by decide
  rcases family_descends (prefixWord ++ tailWord_171899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171922 : List Nat := [3, 2, 3, 2, 1, 1, 2, 4, 1, 3]
def baseStart_171922 : Nat := 118140960795 + 171922 * 2 ^ 59
def prefixEnd_171922 : Nat := 4983230072969 + 3 ^ 40 * 171922 * 2
def baseEnd_171922 : Nat := 58852414054921058722901

theorem tailTrace_171922 : CollatzResearch.WordTrace tailWord_171922 prefixEnd_171922 58852414054921058722901 := by
  unfold tailWord_171922
  simp only [CollatzResearch.WordTrace]
  refine ⟨1567627620790857696271505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4180340322108953856724013 1567627620790857696271505)
  ·
    refine ⟨1175720715593143272203629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1567627620790857696271505 1175720715593143272203629)
    ·
      refine ⟨440895268347428727076361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1175720715593143272203629 440895268347428727076361)
      ·
        refine ⟨330671451260571545307271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 440895268347428727076361 330671451260571545307271)
        ·
          refine ⟨496007176890857317960907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 330671451260571545307271 496007176890857317960907)
          ·
            refine ⟨744010765336285976941361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 496007176890857317960907 744010765336285976941361)
            ·
              refine ⟨558008074002214482706021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 744010765336285976941361 558008074002214482706021)
              ·
                refine ⟨104626513875415215507379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 558008074002214482706021 104626513875415215507379)
                ·
                  refine ⟨156939770813122823261069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 104626513875415215507379 156939770813122823261069)
                  ·
                    refine ⟨58852414054921058722901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 156939770813122823261069 58852414054921058722901)
                    ·
                      rfl

theorem cell22_171922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 2, 4, 1, 3].length) (baseStart_171922 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_171922 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_171922 prefixEnd_171922 := by exact prefixLift 171922
  have htrace : WordTrace (prefixWord ++ tailWord_171922) baseStart_171922 baseEnd_171922 := by
    simpa [prefixWord, tailWord_171922, baseEnd_171922] using wordTrace_append hprefix tailTrace_171922
  have hstable : (prefixWord ++ tailWord_171922).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171922).length < 2 ^ (prefixWord ++ tailWord_171922).sum := by decide
  have hdescent : baseEnd_171922 < baseStart_171922 := by decide
  rcases family_descends (prefixWord ++ tailWord_171922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171935 : List Nat := [1, 1, 2, 5, 3, 1, 3, 1, 5]
def baseStart_171935 : Nat := 118140960795 + 171935 * 2 ^ 59
def prefixEnd_171935 : Nat := 4983230072969 + 3 ^ 40 * 171935 * 2
def baseEnd_171935 : Nat := 19618954740197786049287

theorem tailTrace_171935 : CollatzResearch.WordTrace tailWord_171935 prefixEnd_171935 19618954740197786049287 := by
  unfold tailWord_171935
  simp only [CollatzResearch.WordTrace]
  refine ⟨6270984632116334005309259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4180656421410889336872839 6270984632116334005309259)
  ·
    refine ⟨9406476948174501007963889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6270984632116334005309259 9406476948174501007963889)
    ·
      refine ⟨7054857711130875755972917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9406476948174501007963889 7054857711130875755972917)
      ·
        refine ⟨661392910418519602122461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7054857711130875755972917 661392910418519602122461)
        ·
          refine ⟨248022341406944850795923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 661392910418519602122461 248022341406944850795923)
          ·
            refine ⟨372033512110417276193885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 248022341406944850795923 372033512110417276193885)
            ·
              refine ⟨139512567041406478572707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 372033512110417276193885 139512567041406478572707)
              ·
                refine ⟨209268850562109717859061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 139512567041406478572707 209268850562109717859061)
                ·
                  refine ⟨19618954740197786049287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 209268850562109717859061 19618954740197786049287)
                  ·
                    rfl

theorem cell22_171935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 3, 1, 5].length) (baseStart_171935 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_171935 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_171935 prefixEnd_171935 := by exact prefixLift 171935
  have htrace : WordTrace (prefixWord ++ tailWord_171935) baseStart_171935 baseEnd_171935 := by
    simpa [prefixWord, tailWord_171935, baseEnd_171935] using wordTrace_append hprefix tailTrace_171935
  have hstable : (prefixWord ++ tailWord_171935).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171935).length < 2 ^ (prefixWord ++ tailWord_171935).sum := by decide
  have hdescent : baseEnd_171935 < baseStart_171935 := by decide
  rcases family_descends (prefixWord ++ tailWord_171935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171956 : List Nat := [2, 5, 2, 1, 2, 2, 1, 3, 1, 3]
def baseStart_171956 : Nat := 118140960795 + 171956 * 2 ^ 59
def prefixEnd_171956 : Nat := 4983230072969 + 3 ^ 40 * 171956 * 2
def baseEnd_171956 : Nat := 58864052949756303372797

theorem tailTrace_171956 : CollatzResearch.WordTrace tailWord_171956 prefixEnd_171956 58864052949756303372797 := by
  unfold tailWord_171956
  simp only [CollatzResearch.WordTrace]
  refine ⟨3135875282520127295911861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4181167043360169727882481 3135875282520127295911861)
  ·
    refine ⟨293988307736261933991737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3135875282520127295911861 293988307736261933991737)
    ·
      refine ⟨220491230802196450493803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 293988307736261933991737 220491230802196450493803)
      ·
        refine ⟨330736846203294675740705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 220491230802196450493803 330736846203294675740705)
        ·
          refine ⟨248052634652471006805529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 330736846203294675740705 248052634652471006805529)
          ·
            refine ⟨186039475989353255104147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 248052634652471006805529 186039475989353255104147)
            ·
              refine ⟨279059213984029882656221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 186039475989353255104147 279059213984029882656221)
              ·
                refine ⟨104647205244011205996083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 279059213984029882656221 104647205244011205996083)
                ·
                  refine ⟨156970807866016808994125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 104647205244011205996083 156970807866016808994125)
                  ·
                    refine ⟨58864052949756303372797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 156970807866016808994125 58864052949756303372797)
                    ·
                      rfl

theorem cell22_171956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 1, 3, 1, 3].length) (baseStart_171956 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_171956 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_171956 prefixEnd_171956 := by exact prefixLift 171956
  have htrace : WordTrace (prefixWord ++ tailWord_171956) baseStart_171956 baseEnd_171956 := by
    simpa [prefixWord, tailWord_171956, baseEnd_171956] using wordTrace_append hprefix tailTrace_171956
  have hstable : (prefixWord ++ tailWord_171956).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171956).length < 2 ^ (prefixWord ++ tailWord_171956).sum := by decide
  have hdescent : baseEnd_171956 < baseStart_171956 := by decide
  rcases family_descends (prefixWord ++ tailWord_171956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171961 : List Nat := [1, 2, 1, 4, 2, 1, 2, 1, 3, 5]
def baseStart_171961 : Nat := 118140960795 + 171961 * 2 ^ 59
def prefixEnd_171961 : Nat := 4983230072969 + 3 ^ 40 * 171961 * 2
def baseEnd_171961 : Nat := 58865764551937956997781

theorem tailTrace_171961 : CollatzResearch.WordTrace tailWord_171961 prefixEnd_171961 58865764551937956997781 := by
  unfold tailWord_171961
  simp only [CollatzResearch.WordTrace]
  refine ⟨6271932930022140445755737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4181288620014760297170491 6271932930022140445755737)
  ·
    refine ⟨4703949697516605334316803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6271932930022140445755737 4703949697516605334316803)
    ·
      refine ⟨7055924546274908001475205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4703949697516605334316803 7055924546274908001475205)
      ·
        refine ⟨1322985852426545250276601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7055924546274908001475205 1322985852426545250276601)
        ·
          refine ⟨992239389319908937707451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1322985852426545250276601 992239389319908937707451)
          ·
            refine ⟨1488359083979863406561177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 992239389319908937707451 1488359083979863406561177)
            ·
              refine ⟨1116269312984897554920883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1488359083979863406561177 1116269312984897554920883)
              ·
                refine ⟨1674403969477346332381325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1116269312984897554920883 1674403969477346332381325)
                ·
                  refine ⟨627901488554004874642997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1674403969477346332381325 627901488554004874642997)
                  ·
                    refine ⟨58865764551937956997781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 627901488554004874642997 58865764551937956997781)
                    ·
                      rfl

theorem cell22_171961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 1, 3, 5].length) (baseStart_171961 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_171961 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_171961 prefixEnd_171961 := by exact prefixLift 171961
  have htrace : WordTrace (prefixWord ++ tailWord_171961) baseStart_171961 baseEnd_171961 := by
    simpa [prefixWord, tailWord_171961, baseEnd_171961] using wordTrace_append hprefix tailTrace_171961
  have hstable : (prefixWord ++ tailWord_171961).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171961).length < 2 ^ (prefixWord ++ tailWord_171961).sum := by decide
  have hdescent : baseEnd_171961 < baseStart_171961 := by decide
  rcases family_descends (prefixWord ++ tailWord_171961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171978 : List Nat := [3, 1, 2, 1, 2, 1, 4, 1, 4, 3]
def baseStart_171978 : Nat := 118140960795 + 171978 * 2 ^ 59
def prefixEnd_171978 : Nat := 4983230072969 + 3 ^ 40 * 171978 * 2
def baseEnd_171978 : Nat := 58871583999355579322729

theorem tailTrace_171978 : CollatzResearch.WordTrace tailWord_171978 prefixEnd_171978 58871583999355579322729 := by
  unfold tailWord_171978
  simp only [CollatzResearch.WordTrace]
  refine ⟨1568138242740138087281147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4181701980640368232749725 1568138242740138087281147)
  ·
    refine ⟨2352207364110207130921721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1568138242740138087281147 2352207364110207130921721)
    ·
      refine ⟨1764155523082655348191291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2352207364110207130921721 1764155523082655348191291)
      ·
        refine ⟨2646233284623983022286937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1764155523082655348191291 2646233284623983022286937)
        ·
          refine ⟨1984674963467987266715203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2646233284623983022286937 1984674963467987266715203)
          ·
            refine ⟨2977012445201980900072805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1984674963467987266715203 2977012445201980900072805)
            ·
              refine ⟨558189833475371418763651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2977012445201980900072805 558189833475371418763651)
              ·
                refine ⟨837284750213057128145477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 558189833475371418763651 837284750213057128145477)
                ·
                  refine ⟨156990890664948211527277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 837284750213057128145477 156990890664948211527277)
                  ·
                    refine ⟨58871583999355579322729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 156990890664948211527277 58871583999355579322729)
                    ·
                      rfl

theorem cell22_171978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 4, 1, 4, 3].length) (baseStart_171978 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_171978 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_171978 prefixEnd_171978 := by exact prefixLift 171978
  have htrace : WordTrace (prefixWord ++ tailWord_171978) baseStart_171978 baseEnd_171978 := by
    simpa [prefixWord, tailWord_171978, baseEnd_171978] using wordTrace_append hprefix tailTrace_171978
  have hstable : (prefixWord ++ tailWord_171978).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171978).length < 2 ^ (prefixWord ++ tailWord_171978).sum := by decide
  have hdescent : baseEnd_171978 < baseStart_171978 := by decide
  rcases family_descends (prefixWord ++ tailWord_171978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_171991 : List Nat := [1, 1, 3, 2, 1, 1, 6, 7]
def baseStart_171991 : Nat := 118140960795 + 171991 * 2 ^ 59
def prefixEnd_171991 : Nat := 4983230072969 + 3 ^ 40 * 171991 * 2
def baseEnd_171991 : Nat := 6541781573891986527521

theorem tailTrace_171991 : CollatzResearch.WordTrace tailWord_171991 prefixEnd_171991 6541781573891986527521 := by
  unfold tailWord_171991
  simp only [CollatzResearch.WordTrace]
  refine ⟨6273027119913455569347827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4182018079942303712898551 6273027119913455569347827)
  ·
    refine ⟨9409540679870183354021741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6273027119913455569347827 9409540679870183354021741)
    ·
      refine ⟨3528577754951318757758153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9409540679870183354021741 3528577754951318757758153)
      ·
        refine ⟨2646433316213489068318615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3528577754951318757758153 2646433316213489068318615)
        ·
          refine ⟨3969649974320233602477923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2646433316213489068318615 3969649974320233602477923)
          ·
            refine ⟨5954474961480350403716885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3969649974320233602477923 5954474961480350403716885)
            ·
              refine ⟨279116013819391425174229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 5954474961480350403716885 279116013819391425174229)
              ·
                refine ⟨6541781573891986527521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 279116013819391425174229 6541781573891986527521)
                ·
                  rfl

theorem cell22_171991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 6, 7].length) (baseStart_171991 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_171991 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_171991 prefixEnd_171991 := by exact prefixLift 171991
  have htrace : WordTrace (prefixWord ++ tailWord_171991) baseStart_171991 baseEnd_171991 := by
    simpa [prefixWord, tailWord_171991, baseEnd_171991] using wordTrace_append hprefix tailTrace_171991
  have hstable : (prefixWord ++ tailWord_171991).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_171991).length < 2 ^ (prefixWord ++ tailWord_171991).sum := by decide
  have hdescent : baseEnd_171991 < baseStart_171991 := by decide
  rcases family_descends (prefixWord ++ tailWord_171991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172051 : List Nat := [1, 1, 1, 2, 1, 4, 3, 1, 1, 7]
def baseStart_172051 : Nat := 118140960795 + 172051 * 2 ^ 59
def prefixEnd_172051 : Nat := 4983230072969 + 3 ^ 40 * 172051 * 2
def baseEnd_172051 : Nat := 58896573391207722247505

theorem tailTrace_172051 : CollatzResearch.WordTrace tailWord_172051 prefixEnd_172051 58896573391207722247505 := by
  unfold tailWord_172051
  simp only [CollatzResearch.WordTrace]
  refine ⟨6275215499696085816532007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4183476999797390544354671 6275215499696085816532007)
  ·
    refine ⟨9412823249544128724798011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6275215499696085816532007 9412823249544128724798011)
    ·
      refine ⟨14119234874316193087197017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9412823249544128724798011 14119234874316193087197017)
      ·
        refine ⟨10589426155737144815397763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14119234874316193087197017 10589426155737144815397763)
        ·
          refine ⟨15884139233605717223096645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10589426155737144815397763 15884139233605717223096645)
          ·
            refine ⟨2978276106301071979330621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15884139233605717223096645 2978276106301071979330621)
            ·
              refine ⟨1116853539862901992248983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2978276106301071979330621 1116853539862901992248983)
              ·
                refine ⟨1675280309794352988373475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1116853539862901992248983 1675280309794352988373475)
                ·
                  refine ⟨2512920464691529482560213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1675280309794352988373475 2512920464691529482560213)
                  ·
                    refine ⟨58896573391207722247505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2512920464691529482560213 58896573391207722247505)
                    ·
                      rfl

theorem cell22_172051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 1, 1, 7].length) (baseStart_172051 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_172051 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_172051 prefixEnd_172051 := by exact prefixLift 172051
  have htrace : WordTrace (prefixWord ++ tailWord_172051) baseStart_172051 baseEnd_172051 := by
    simpa [prefixWord, tailWord_172051, baseEnd_172051] using wordTrace_append hprefix tailTrace_172051
  have hstable : (prefixWord ++ tailWord_172051).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172051).length < 2 ^ (prefixWord ++ tailWord_172051).sum := by decide
  have hdescent : baseEnd_172051 < baseStart_172051 := by decide
  rcases family_descends (prefixWord ++ tailWord_172051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172074 : List Nat := [3, 1, 4, 1, 2, 2, 2, 3, 1, 3]
def baseStart_172074 : Nat := 118140960795 + 172074 * 2 ^ 59
def prefixEnd_172074 : Nat := 4983230072969 + 3 ^ 40 * 172074 * 2
def baseEnd_172074 : Nat := 58904446761243328922435

theorem tailTrace_172074 : CollatzResearch.WordTrace tailWord_172074 prefixEnd_172074 58904446761243328922435 := by
  unfold tailWord_172074
  simp only [CollatzResearch.WordTrace]
  refine ⟨1569013594653190186154819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4184036252408507163079517 1569013594653190186154819)
  ·
    refine ⟨2353520391979785279232229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1569013594653190186154819 2353520391979785279232229)
    ·
      refine ⟨441285073496209739856043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2353520391979785279232229 441285073496209739856043)
      ·
        refine ⟨661927610244314609784065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 441285073496209739856043 661927610244314609784065)
        ·
          refine ⟨496445707683235957338049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 661927610244314609784065 496445707683235957338049)
          ·
            refine ⟨372334280762426968003537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 496445707683235957338049 372334280762426968003537)
            ·
              refine ⟨279250710571820226002653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 372334280762426968003537 279250710571820226002653)
              ·
                refine ⟨104719016464432584750995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 279250710571820226002653 104719016464432584750995)
                ·
                  refine ⟨157078524696648877126493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 104719016464432584750995 157078524696648877126493)
                  ·
                    refine ⟨58904446761243328922435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 157078524696648877126493 58904446761243328922435)
                    ·
                      rfl

theorem cell22_172074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 2, 3, 1, 3].length) (baseStart_172074 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_172074 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_172074 prefixEnd_172074 := by exact prefixLift 172074
  have htrace : WordTrace (prefixWord ++ tailWord_172074) baseStart_172074 baseEnd_172074 := by
    simpa [prefixWord, tailWord_172074, baseEnd_172074] using wordTrace_append hprefix tailTrace_172074
  have hstable : (prefixWord ++ tailWord_172074).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172074).length < 2 ^ (prefixWord ++ tailWord_172074).sum := by decide
  have hdescent : baseEnd_172074 < baseStart_172074 := by decide
  rcases family_descends (prefixWord ++ tailWord_172074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172128 : List Nat := [2, 1, 1, 3, 2, 3, 2, 1, 1, 6]
def baseStart_172128 : Nat := 118140960795 + 172128 * 2 ^ 59
def prefixEnd_172128 : Nat := 4983230072969 + 3 ^ 40 * 172128 * 2
def baseEnd_172128 : Nat := 58922932064805188072269

theorem tailTrace_172128 : CollatzResearch.WordTrace tailWord_172128 prefixEnd_172128 58922932064805188072269 := by
  unfold tailWord_172128
  simp only [CollatzResearch.WordTrace]
  refine ⟨3139011960208563983542519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4185349280278085311390025 3139011960208563983542519)
  ·
    refine ⟨4708517940312845975313779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3139011960208563983542519 4708517940312845975313779)
    ·
      refine ⟨7062776910469268962970669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4708517940312845975313779 7062776910469268962970669)
      ·
        refine ⟨2648541341425975861114001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7062776910469268962970669 2648541341425975861114001)
        ·
          refine ⟨1986406006069481895835501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2648541341425975861114001 1986406006069481895835501)
          ·
            refine ⟨744902252276055710938313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1986406006069481895835501 744902252276055710938313)
            ·
              refine ⟨558676689207041783203735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 744902252276055710938313 558676689207041783203735)
              ·
                refine ⟨838015033810562674805603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 558676689207041783203735 838015033810562674805603)
                ·
                  refine ⟨1257022550715844012208405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 838015033810562674805603 1257022550715844012208405)
                  ·
                    refine ⟨58922932064805188072269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1257022550715844012208405 58922932064805188072269)
                    ·
                      rfl

theorem cell22_172128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 2, 1, 1, 6].length) (baseStart_172128 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_172128 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_172128 prefixEnd_172128 := by exact prefixLift 172128
  have htrace : WordTrace (prefixWord ++ tailWord_172128) baseStart_172128 baseEnd_172128 := by
    simpa [prefixWord, tailWord_172128, baseEnd_172128] using wordTrace_append hprefix tailTrace_172128
  have hstable : (prefixWord ++ tailWord_172128).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172128).length < 2 ^ (prefixWord ++ tailWord_172128).sum := by decide
  have hdescent : baseEnd_172128 < baseStart_172128 := by decide
  rcases family_descends (prefixWord ++ tailWord_172128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172143 : List Nat := [1, 1, 2, 1, 3, 6, 8]
def baseStart_172143 : Nat := 118140960795 + 172143 * 2 ^ 59
def prefixEnd_172143 : Nat := 4983230072969 + 3 ^ 40 * 172143 * 2
def baseEnd_172143 : Nat := 2182520995235190701749

theorem tailTrace_172143 : CollatzResearch.WordTrace tailWord_172143 prefixEnd_172143 2182520995235190701749 := by
  unfold tailWord_172143
  simp only [CollatzResearch.WordTrace]
  refine ⟨6278571015362785528881083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4185714010241857019254055 6278571015362785528881083)
  ·
    refine ⟨9417856523044178293321625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6278571015362785528881083 9417856523044178293321625)
    ·
      refine ⟨7063392392283133719991219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9417856523044178293321625 7063392392283133719991219)
      ·
        refine ⟨10595088588424700579986829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7063392392283133719991219 10595088588424700579986829)
        ·
          refine ⟨3973158220659262717495061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10595088588424700579986829 3973158220659262717495061)
          ·
            refine ⟨186241791593402939882581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 3973158220659262717495061 186241791593402939882581)
            ·
              refine ⟨2182520995235190701749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 186241791593402939882581 2182520995235190701749)
              ·
                rfl

theorem cell22_172143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 8].length) (baseStart_172143 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_172143 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_172143 prefixEnd_172143 := by exact prefixLift 172143
  have htrace : WordTrace (prefixWord ++ tailWord_172143) baseStart_172143 baseEnd_172143 := by
    simpa [prefixWord, tailWord_172143, baseEnd_172143] using wordTrace_append hprefix tailTrace_172143
  have hstable : (prefixWord ++ tailWord_172143).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172143).length < 2 ^ (prefixWord ++ tailWord_172143).sum := by decide
  have hdescent : baseEnd_172143 < baseStart_172143 := by decide
  rcases family_descends (prefixWord ++ tailWord_172143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172226 : List Nat := [3, 5, 1, 1, 1, 2, 1, 2, 3, 3]
def baseStart_172226 : Nat := 118140960795 + 172226 * 2 ^ 59
def prefixEnd_172226 : Nat := 4983230072969 + 3 ^ 40 * 172226 * 2
def baseEnd_172226 : Nat := 58956479467565599121969

theorem tailTrace_172226 : CollatzResearch.WordTrace tailWord_172226 prefixEnd_172226 58956479467565599121969 := by
  unfold tailWord_172226
  simp only [CollatzResearch.WordTrace]
  refine ⟨1570399568515522676038133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4187732182708060469435021 1570399568515522676038133)
  ·
    refine ⟨147224959548330250878575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1570399568515522676038133 147224959548330250878575)
    ·
      refine ⟨220837439322495376317863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147224959548330250878575 220837439322495376317863)
      ·
        refine ⟨331256158983743064476795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 220837439322495376317863 331256158983743064476795)
        ·
          refine ⟨496884238475614596715193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 331256158983743064476795 496884238475614596715193)
          ·
            refine ⟨372663178856710947536395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 496884238475614596715193 372663178856710947536395)
            ·
              refine ⟨558994768285066421304593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 372663178856710947536395 558994768285066421304593)
              ·
                refine ⟨419246076213799815978445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 558994768285066421304593 419246076213799815978445)
                ·
                  refine ⟨157217278580174930991917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 419246076213799815978445 157217278580174930991917)
                  ·
                    refine ⟨58956479467565599121969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 157217278580174930991917 58956479467565599121969)
                    ·
                      rfl

theorem cell22_172226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 1, 2, 3, 3].length) (baseStart_172226 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_172226 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_172226 prefixEnd_172226 := by exact prefixLift 172226
  have htrace : WordTrace (prefixWord ++ tailWord_172226) baseStart_172226 baseEnd_172226 := by
    simpa [prefixWord, tailWord_172226, baseEnd_172226] using wordTrace_append hprefix tailTrace_172226
  have hstable : (prefixWord ++ tailWord_172226).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172226).length < 2 ^ (prefixWord ++ tailWord_172226).sum := by decide
  have hdescent : baseEnd_172226 < baseStart_172226 := by decide
  rcases family_descends (prefixWord ++ tailWord_172226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172235 : List Nat := [1, 1, 1, 1, 3, 2, 4, 4, 1, 4]
def baseStart_172235 : Nat := 118140960795 + 172235 * 2 ^ 59
def prefixEnd_172235 : Nat := 4983230072969 + 3 ^ 40 * 172235 * 2
def baseEnd_172235 : Nat := 58959560351492575646941

theorem tailTrace_172235 : CollatzResearch.WordTrace tailWord_172235 prefixEnd_172235 58959560351492575646941 := by
  unfold tailWord_172235
  simp only [CollatzResearch.WordTrace]
  refine ⟨6281926531029485241230159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4187951020686323494153439 6281926531029485241230159)
  ·
    refine ⟨9422889796544227861845239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6281926531029485241230159 9422889796544227861845239)
    ·
      refine ⟨14134334694816341792767859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9422889796544227861845239 14134334694816341792767859)
      ·
        refine ⟨21201502042224512689151789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14134334694816341792767859 21201502042224512689151789)
        ·
          refine ⟨7950563265834192258431921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21201502042224512689151789 7950563265834192258431921)
          ·
            refine ⟨5962922449375644193823941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7950563265834192258431921 5962922449375644193823941)
            ·
              refine ⟨1118047959257933286341989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5962922449375644193823941 1118047959257933286341989)
              ·
                refine ⟨209633992360862491189123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1118047959257933286341989 209633992360862491189123)
                ·
                  refine ⟨314450988541293736783685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 209633992360862491189123 314450988541293736783685)
                  ·
                    refine ⟨58959560351492575646941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 314450988541293736783685 58959560351492575646941)
                    ·
                      rfl

theorem cell22_172235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 4, 1, 4].length) (baseStart_172235 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_172235 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_172235 prefixEnd_172235 := by exact prefixLift 172235
  have htrace : WordTrace (prefixWord ++ tailWord_172235) baseStart_172235 baseEnd_172235 := by
    simpa [prefixWord, tailWord_172235, baseEnd_172235] using wordTrace_append hprefix tailTrace_172235
  have hstable : (prefixWord ++ tailWord_172235).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172235).length < 2 ^ (prefixWord ++ tailWord_172235).sum := by decide
  have hdescent : baseEnd_172235 < baseStart_172235 := by decide
  rcases family_descends (prefixWord ++ tailWord_172235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172265 : List Nat := [1, 2, 1, 1, 1, 2, 2, 5, 4, 3]
def baseStart_172265 : Nat := 118140960795 + 172265 * 2 ^ 59
def prefixEnd_172265 : Nat := 4983230072969 + 3 ^ 40 * 172265 * 2
def baseEnd_172265 : Nat := 58969829964582497396849

theorem tailTrace_172265 : CollatzResearch.WordTrace tailWord_172265 prefixEnd_172265 58969829964582497396849 := by
  unfold tailWord_172265
  simp only [CollatzResearch.WordTrace]
  refine ⟨6283020720920800364822249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4188680480613866909881499 6283020720920800364822249)
  ·
    refine ⟨4712265540690600273616687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6283020720920800364822249 4712265540690600273616687)
    ·
      refine ⟨7068398311035900410425031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4712265540690600273616687 7068398311035900410425031)
      ·
        refine ⟨10602597466553850615637547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7068398311035900410425031 10602597466553850615637547)
        ·
          refine ⟨15903896199830775923456321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10602597466553850615637547 15903896199830775923456321)
          ·
            refine ⟨11927922149873081942592241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15903896199830775923456321 11927922149873081942592241)
            ·
              refine ⟨8945941612404811456944181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11927922149873081942592241 8945941612404811456944181)
              ·
                refine ⟨838682026162951074088517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8945941612404811456944181 838682026162951074088517)
                ·
                  refine ⟨157252879905553326391597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 838682026162951074088517 157252879905553326391597)
                  ·
                    refine ⟨58969829964582497396849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 157252879905553326391597 58969829964582497396849)
                    ·
                      rfl

theorem cell22_172265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 5, 4, 3].length) (baseStart_172265 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_172265 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_172265 prefixEnd_172265 := by exact prefixLift 172265
  have htrace : WordTrace (prefixWord ++ tailWord_172265) baseStart_172265 baseEnd_172265 := by
    simpa [prefixWord, tailWord_172265, baseEnd_172265] using wordTrace_append hprefix tailTrace_172265
  have hstable : (prefixWord ++ tailWord_172265).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172265).length < 2 ^ (prefixWord ++ tailWord_172265).sum := by decide
  have hdescent : baseEnd_172265 < baseStart_172265 := by decide
  rcases family_descends (prefixWord ++ tailWord_172265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172282 : List Nat := [3, 1, 1, 1, 1, 7, 1, 1, 1, 5]
def baseStart_172282 : Nat := 118140960795 + 172282 * 2 ^ 59
def prefixEnd_172282 : Nat := 4983230072969 + 3 ^ 40 * 172282 * 2
def baseEnd_172282 : Nat := 58975649412000119721797

theorem tailTrace_172282 : CollatzResearch.WordTrace tailWord_172282 prefixEnd_172282 58975649412000119721797 := by
  unfold tailWord_172282
  simp only [CollatzResearch.WordTrace]
  refine ⟨1570910190464803067047775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4189093841239474845460733 1570910190464803067047775)
  ·
    refine ⟨2356365285697204600571663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1570910190464803067047775 2356365285697204600571663)
    ·
      refine ⟨3534547928545806900857495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2356365285697204600571663 3534547928545806900857495)
      ·
        refine ⟨5301821892818710351286243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3534547928545806900857495 5301821892818710351286243)
        ·
          refine ⟨7952732839228065526929365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5301821892818710351286243 7952732839228065526929365)
          ·
            refine ⟨186392175919407785787407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 7952732839228065526929365 186392175919407785787407)
            ·
              refine ⟨279588263879111678681111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 186392175919407785787407 279588263879111678681111)
              ·
                refine ⟨419382395818667518021667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 279588263879111678681111 419382395818667518021667)
                ·
                  refine ⟨629073593728001277032501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 419382395818667518021667 629073593728001277032501)
                  ·
                    refine ⟨58975649412000119721797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 629073593728001277032501 58975649412000119721797)
                    ·
                      rfl

theorem cell22_172282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 1, 1, 1, 5].length) (baseStart_172282 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_172282 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_172282 prefixEnd_172282 := by exact prefixLift 172282
  have htrace : WordTrace (prefixWord ++ tailWord_172282) baseStart_172282 baseEnd_172282 := by
    simpa [prefixWord, tailWord_172282, baseEnd_172282] using wordTrace_append hprefix tailTrace_172282
  have hstable : (prefixWord ++ tailWord_172282).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172282).length < 2 ^ (prefixWord ++ tailWord_172282).sum := by decide
  have hdescent : baseEnd_172282 < baseStart_172282 := by decide
  rcases family_descends (prefixWord ++ tailWord_172282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172318 : List Nat := [4, 3, 2, 1, 1, 2, 3, 2, 4]
def baseStart_172318 : Nat := 118140960795 + 172318 * 2 ^ 59
def prefixEnd_172318 : Nat := 4983230072969 + 3 ^ 40 * 172318 * 2
def baseEnd_172318 : Nat := 19662657649236008607229

theorem tailTrace_172318 : CollatzResearch.WordTrace tailWord_172318 prefixEnd_172318 19662657649236008607229 := by
  unfold tailWord_172318
  simp only [CollatzResearch.WordTrace]
  refine ⟨785619223716098802062701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4189969193152526944334405 785619223716098802062701)
  ·
    refine ⟨294607208893537050773513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 785619223716098802062701 294607208893537050773513)
    ·
      refine ⟨220955406670152788080135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 294607208893537050773513 220955406670152788080135)
      ·
        refine ⟨331433110005229182120203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 220955406670152788080135 331433110005229182120203)
        ·
          refine ⟨497149665007843773180305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 331433110005229182120203 497149665007843773180305)
          ·
            refine ⟨372862248755882829885229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 497149665007843773180305 372862248755882829885229)
            ·
              refine ⟨139823343283456061206961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 372862248755882829885229 139823343283456061206961)
              ·
                refine ⟨104867507462592045905221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 139823343283456061206961 104867507462592045905221)
                ·
                  refine ⟨19662657649236008607229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 104867507462592045905221 19662657649236008607229)
                  ·
                    rfl

theorem cell22_172318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 3, 2, 4].length) (baseStart_172318 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_172318 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_172318 prefixEnd_172318 := by exact prefixLift 172318
  have htrace : WordTrace (prefixWord ++ tailWord_172318) baseStart_172318 baseEnd_172318 := by
    simpa [prefixWord, tailWord_172318, baseEnd_172318] using wordTrace_append hprefix tailTrace_172318
  have hstable : (prefixWord ++ tailWord_172318).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172318).length < 2 ^ (prefixWord ++ tailWord_172318).sum := by decide
  have hdescent : baseEnd_172318 < baseStart_172318 := by decide
  rcases family_descends (prefixWord ++ tailWord_172318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172402 : List Nat := [3, 2, 1, 2, 1, 4, 1, 2, 6]
def baseStart_172402 : Nat := 118140960795 + 172402 * 2 ^ 59
def prefixEnd_172402 : Nat := 4983230072969 + 3 ^ 40 * 172402 * 2
def baseEnd_172402 : Nat := 19672242621453268907143

theorem tailTrace_172402 : CollatzResearch.WordTrace tailWord_172402 prefixEnd_172402 19672242621453268907143 := by
  unfold tailWord_172402
  simp only [CollatzResearch.WordTrace]
  refine ⟨1572004380356118190639865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4192011680949648508372973 1572004380356118190639865)
  ·
    refine ⟨1179003285267088642979899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1572004380356118190639865 1179003285267088642979899)
    ·
      refine ⟨1768504927900632964469849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1179003285267088642979899 1768504927900632964469849)
      ·
        refine ⟨1326378695925474723352387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1768504927900632964469849 1326378695925474723352387)
        ·
          refine ⟨1989568043888212085028581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1326378695925474723352387 1989568043888212085028581)
          ·
            refine ⟨373044008229039765942859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1989568043888212085028581 373044008229039765942859)
            ·
              refine ⟨559566012343559648914289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 373044008229039765942859 559566012343559648914289)
              ·
                refine ⟨419674509257669736685717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 559566012343559648914289 419674509257669736685717)
                ·
                  refine ⟨19672242621453268907143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 419674509257669736685717 19672242621453268907143)
                  ·
                    rfl

theorem cell22_172402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 1, 2, 6].length) (baseStart_172402 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_172402 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_172402 prefixEnd_172402 := by exact prefixLift 172402
  have htrace : WordTrace (prefixWord ++ tailWord_172402) baseStart_172402 baseEnd_172402 := by
    simpa [prefixWord, tailWord_172402, baseEnd_172402] using wordTrace_append hprefix tailTrace_172402
  have hstable : (prefixWord ++ tailWord_172402).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172402).length < 2 ^ (prefixWord ++ tailWord_172402).sum := by decide
  have hdescent : baseEnd_172402 < baseStart_172402 := by decide
  rcases family_descends (prefixWord ++ tailWord_172402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172415 : List Nat := [1, 1, 2, 2, 1, 1, 2, 5, 1, 6]
def baseStart_172415 : Nat := 118140960795 + 172415 * 2 ^ 59
def prefixEnd_172415 : Nat := 4983230072969 + 3 ^ 40 * 172415 * 2
def baseEnd_172415 : Nat := 59021178030032106146389

theorem tailTrace_172415 : CollatzResearch.WordTrace tailWord_172415 prefixEnd_172415 59021178030032106146389 := by
  unfold tailWord_172415
  simp only [CollatzResearch.WordTrace]
  refine ⟨6288491670377375982782699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4192327780251583988521799 6288491670377375982782699)
  ·
    refine ⟨9432737505566063974174049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6288491670377375982782699 9432737505566063974174049)
    ·
      refine ⟨7074553129174547980630537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9432737505566063974174049 7074553129174547980630537)
      ·
        refine ⟨5305914846880910985472903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7074553129174547980630537 5305914846880910985472903)
        ·
          refine ⟨7958872270321366478209355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5305914846880910985472903 7958872270321366478209355)
          ·
            refine ⟨11938308405482049717314033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7958872270321366478209355 11938308405482049717314033)
            ·
              refine ⟨8953731304111537287985525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11938308405482049717314033 8953731304111537287985525)
              ·
                refine ⟨839412309760456620748643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8953731304111537287985525 839412309760456620748643)
                ·
                  refine ⟨1259118464640684931122965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 839412309760456620748643 1259118464640684931122965)
                  ·
                    refine ⟨59021178030032106146389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1259118464640684931122965 59021178030032106146389)
                    ·
                      rfl

theorem cell22_172415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 5, 1, 6].length) (baseStart_172415 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_172415 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_172415 prefixEnd_172415 := by exact prefixLift 172415
  have htrace : WordTrace (prefixWord ++ tailWord_172415) baseStart_172415 baseEnd_172415 := by
    simpa [prefixWord, tailWord_172415, baseEnd_172415] using wordTrace_append hprefix tailTrace_172415
  have hstable : (prefixWord ++ tailWord_172415).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172415).length < 2 ^ (prefixWord ++ tailWord_172415).sum := by decide
  have hdescent : baseEnd_172415 < baseStart_172415 := by decide
  rcases family_descends (prefixWord ++ tailWord_172415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172451 : List Nat := [1, 1, 1, 4, 1, 5, 3, 1, 2, 3]
def baseStart_172451 : Nat := 118140960795 + 172451 * 2 ^ 59
def prefixEnd_172451 : Nat := 4983230072969 + 3 ^ 40 * 172451 * 2
def baseEnd_172451 : Nat := 59033501565740012246279

theorem tailTrace_172451 : CollatzResearch.WordTrace tailWord_172451 prefixEnd_172451 59033501565740012246279 := by
  unfold tailWord_172451
  simp only [CollatzResearch.WordTrace]
  refine ⟨6289804698246954131093207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4193203132164636087395471 6289804698246954131093207)
  ·
    refine ⟨9434707047370431196639811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6289804698246954131093207 9434707047370431196639811)
    ·
      refine ⟨14152060571055646794959717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9434707047370431196639811 14152060571055646794959717)
      ·
        refine ⟨2653511357072933774054947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14152060571055646794959717 2653511357072933774054947)
        ·
          refine ⟨3980267035609400661082421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2653511357072933774054947 3980267035609400661082421)
          ·
            refine ⟨373150034588381311976477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3980267035609400661082421 373150034588381311976477)
            ·
              refine ⟨139931262970642991991179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 373150034588381311976477 139931262970642991991179)
              ·
                refine ⟨209896894455964487986769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 139931262970642991991179 209896894455964487986769)
                ·
                  refine ⟨157422670841973365990077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 209896894455964487986769 157422670841973365990077)
                  ·
                    refine ⟨59033501565740012246279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 157422670841973365990077 59033501565740012246279)
                    ·
                      rfl

theorem cell22_172451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 3, 1, 2, 3].length) (baseStart_172451 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_172451 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_172451 prefixEnd_172451 := by exact prefixLift 172451
  have htrace : WordTrace (prefixWord ++ tailWord_172451) baseStart_172451 baseEnd_172451 := by
    simpa [prefixWord, tailWord_172451, baseEnd_172451] using wordTrace_append hprefix tailTrace_172451
  have hstable : (prefixWord ++ tailWord_172451).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172451).length < 2 ^ (prefixWord ++ tailWord_172451).sum := by decide
  have hdescent : baseEnd_172451 < baseStart_172451 := by decide
  rcases family_descends (prefixWord ++ tailWord_172451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172509 : List Nat := [1, 4, 3, 1, 1, 1, 3, 3, 5]
def baseStart_172509 : Nat := 118140960795 + 172509 * 2 ^ 59
def prefixEnd_172509 : Nat := 4983230072969 + 3 ^ 40 * 172509 * 2
def baseEnd_172509 : Nat := 19684452050349064765367

theorem tailTrace_172509 : CollatzResearch.WordTrace tailWord_172509 prefixEnd_172509 19684452050349064765367 := by
  unfold tailWord_172509
  simp only [CollatzResearch.WordTrace]
  refine ⟨6291920132036830036704581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4194613421357886691136387 6291920132036830036704581)
  ·
    refine ⟨1179735024756905631882109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6291920132036830036704581 1179735024756905631882109)
    ·
      refine ⟨442400634283839611955791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1179735024756905631882109 442400634283839611955791)
      ·
        refine ⟨663600951425759417933687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 442400634283839611955791 663600951425759417933687)
        ·
          refine ⟨995401427138639126900531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 663600951425759417933687 995401427138639126900531)
          ·
            refine ⟨1493102140707958690350797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 995401427138639126900531 1493102140707958690350797)
            ·
              refine ⟨559913302765484508881549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1493102140707958690350797 559913302765484508881549)
              ·
                refine ⟨209967488537056690830581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 559913302765484508881549 209967488537056690830581)
                ·
                  refine ⟨19684452050349064765367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 209967488537056690830581 19684452050349064765367)
                  ·
                    rfl

theorem cell22_172509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 3, 3, 5].length) (baseStart_172509 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_172509 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_172509 prefixEnd_172509 := by exact prefixLift 172509
  have htrace : WordTrace (prefixWord ++ tailWord_172509) baseStart_172509 baseEnd_172509 := by
    simpa [prefixWord, tailWord_172509, baseEnd_172509] using wordTrace_append hprefix tailTrace_172509
  have hstable : (prefixWord ++ tailWord_172509).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172509).length < 2 ^ (prefixWord ++ tailWord_172509).sum := by decide
  have hdescent : baseEnd_172509 < baseStart_172509 := by decide
  rcases family_descends (prefixWord ++ tailWord_172509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172552 : List Nat := [2, 1, 3, 2, 1, 1, 1, 1, 5, 5]
def baseStart_172552 : Nat := 118140960795 + 172552 * 2 ^ 59
def prefixEnd_172552 : Nat := 4983230072969 + 3 ^ 40 * 172552 * 2
def baseEnd_172552 : Nat := 59068075929809415470969

theorem tailTrace_172552 : CollatzResearch.WordTrace tailWord_172552 prefixEnd_172552 59068075929809415470969 := by
  unfold tailWord_172552
  simp only [CollatzResearch.WordTrace]
  refine ⟨3146744235440524190259955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4195658980587365587013273 3146744235440524190259955)
  ·
    refine ⟨4720116353160786285389933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3146744235440524190259955 4720116353160786285389933)
    ·
      refine ⟨1770043632435294857021225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4720116353160786285389933 1770043632435294857021225)
      ·
        refine ⟨1327532724326471142765919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1770043632435294857021225 1327532724326471142765919)
        ·
          refine ⟨1991299086489706714148879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1327532724326471142765919 1991299086489706714148879)
          ·
            refine ⟨2986948629734560071223319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1991299086489706714148879 2986948629734560071223319)
            ·
              refine ⟨4480422944601840106834979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2986948629734560071223319 4480422944601840106834979)
              ·
                refine ⟨6720634416902760160252469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4480422944601840106834979 6720634416902760160252469)
                ·
                  refine ⟨630059476584633765023669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 6720634416902760160252469 630059476584633765023669)
                  ·
                    refine ⟨59068075929809415470969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 630059476584633765023669 59068075929809415470969)
                    ·
                      rfl

theorem cell22_172552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 1, 5, 5].length) (baseStart_172552 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_172552 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_172552 prefixEnd_172552 := by exact prefixLift 172552
  have htrace : WordTrace (prefixWord ++ tailWord_172552) baseStart_172552 baseEnd_172552 := by
    simpa [prefixWord, tailWord_172552, baseEnd_172552] using wordTrace_append hprefix tailTrace_172552
  have hstable : (prefixWord ++ tailWord_172552).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172552).length < 2 ^ (prefixWord ++ tailWord_172552).sum := by decide
  have hdescent : baseEnd_172552 < baseStart_172552 := by decide
  rcases family_descends (prefixWord ++ tailWord_172552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172590 : List Nat := [4, 1, 3, 1, 3, 2, 2, 1, 1, 4]
def baseStart_172590 : Nat := 118140960795 + 172590 * 2 ^ 59
def prefixEnd_172590 : Nat := 4983230072969 + 3 ^ 40 * 172590 * 2
def baseEnd_172590 : Nat := 59081084106389983020853

theorem tailTrace_172590 : CollatzResearch.WordTrace tailWord_172590 prefixEnd_172590 59081084106389983020853 := by
  unfold tailWord_172590
  simp only [CollatzResearch.WordTrace]
  refine ⟨786859305592922608800403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4196582963162253913602149 786859305592922608800403)
  ·
    refine ⟨1180288958389383913200605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 786859305592922608800403 1180288958389383913200605)
    ·
      refine ⟨442608359396018967450227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1180288958389383913200605 442608359396018967450227)
      ·
        refine ⟨663912539094028451175341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 442608359396018967450227 663912539094028451175341)
        ·
          refine ⟨248967202160260669190753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 663912539094028451175341 248967202160260669190753)
          ·
            refine ⟨186725401620195501893065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 248967202160260669190753 186725401620195501893065)
            ·
              refine ⟨140044051215146626419799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 186725401620195501893065 140044051215146626419799)
              ·
                refine ⟨210066076822719939629699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 140044051215146626419799 210066076822719939629699)
                ·
                  refine ⟨315099115234079909444549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 210066076822719939629699 315099115234079909444549)
                  ·
                    refine ⟨59081084106389983020853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 315099115234079909444549 59081084106389983020853)
                    ·
                      rfl

theorem cell22_172590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 2, 1, 1, 4].length) (baseStart_172590 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_172590 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_172590 prefixEnd_172590 := by exact prefixLift 172590
  have htrace : WordTrace (prefixWord ++ tailWord_172590) baseStart_172590 baseEnd_172590 := by
    simpa [prefixWord, tailWord_172590, baseEnd_172590] using wordTrace_append hprefix tailTrace_172590
  have hstable : (prefixWord ++ tailWord_172590).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172590).length < 2 ^ (prefixWord ++ tailWord_172590).sum := by decide
  have hdescent : baseEnd_172590 < baseStart_172590 := by decide
  rcases family_descends (prefixWord ++ tailWord_172590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172665 : List Nat := [1, 2, 1, 3, 3, 3, 3, 2, 1, 3]
def baseStart_172665 : Nat := 118140960795 + 172665 * 2 ^ 59
def prefixEnd_172665 : Nat := 4983230072969 + 3 ^ 40 * 172665 * 2
def baseEnd_172665 : Nat := 59106758139114787395623

theorem tailTrace_172665 : CollatzResearch.WordTrace tailWord_172665 prefixEnd_172665 59106758139114787395623 := by
  unfold tailWord_172665
  simp only [CollatzResearch.WordTrace]
  refine ⟨6297609919471668679383449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4198406612981112452922299 6297609919471668679383449)
  ·
    refine ⟨4723207439603751509537587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6297609919471668679383449 4723207439603751509537587)
    ·
      refine ⟨7084811159405627264306381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4723207439603751509537587 7084811159405627264306381)
      ·
        refine ⟨2656804184777110224114893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7084811159405627264306381 2656804184777110224114893)
        ·
          refine ⟨996301569291416334043085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2656804184777110224114893 996301569291416334043085)
          ·
            refine ⟨373613088484281125266157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 996301569291416334043085 373613088484281125266157)
            ·
              refine ⟨140104908181605421974809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 373613088484281125266157 140104908181605421974809)
              ·
                refine ⟨105078681136204066481107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 140104908181605421974809 105078681136204066481107)
                ·
                  refine ⟨157618021704306099721661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 105078681136204066481107 157618021704306099721661)
                  ·
                    refine ⟨59106758139114787395623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 157618021704306099721661 59106758139114787395623)
                    ·
                      rfl

theorem cell22_172665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 3, 2, 1, 3].length) (baseStart_172665 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_172665 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_172665 prefixEnd_172665 := by exact prefixLift 172665
  have htrace : WordTrace (prefixWord ++ tailWord_172665) baseStart_172665 baseEnd_172665 := by
    simpa [prefixWord, tailWord_172665, baseEnd_172665] using wordTrace_append hprefix tailTrace_172665
  have hstable : (prefixWord ++ tailWord_172665).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172665).length < 2 ^ (prefixWord ++ tailWord_172665).sum := by decide
  have hdescent : baseEnd_172665 < baseStart_172665 := by decide
  rcases family_descends (prefixWord ++ tailWord_172665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172708 : List Nat := [2, 3, 1, 2, 2, 1, 5, 1, 1, 4]
def baseStart_172708 : Nat := 118140960795 + 172708 * 2 ^ 59
def prefixEnd_172708 : Nat := 4983230072969 + 3 ^ 40 * 172708 * 2
def baseEnd_172708 : Nat := 59121477917877008570491

theorem tailTrace_172708 : CollatzResearch.WordTrace tailWord_172708 prefixEnd_172708 59121477917877008570491 := by
  unfold tailWord_172708
  simp only [CollatzResearch.WordTrace]
  refine ⟨3149589129157943511599389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4199452172210591348799185 3149589129157943511599389)
  ·
    refine ⟨1181095923434228816849771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3149589129157943511599389 1181095923434228816849771)
    ·
      refine ⟨1771643885151343225274657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1181095923434228816849771 1771643885151343225274657)
      ·
        refine ⟨1328732913863507418955993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1771643885151343225274657 1328732913863507418955993)
        ·
          refine ⟨996549685397630564216995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1328732913863507418955993 996549685397630564216995)
          ·
            refine ⟨1494824528096445846325493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 996549685397630564216995 1494824528096445846325493)
            ·
              refine ⟨140139799509041798093015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1494824528096445846325493 140139799509041798093015)
              ·
                refine ⟨210209699263562697139523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 140139799509041798093015 210209699263562697139523)
                ·
                  refine ⟨315314548895344045709285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 210209699263562697139523 315314548895344045709285)
                  ·
                    refine ⟨59121477917877008570491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 315314548895344045709285 59121477917877008570491)
                    ·
                      rfl

theorem cell22_172708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 5, 1, 1, 4].length) (baseStart_172708 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_172708 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_172708 prefixEnd_172708 := by exact prefixLift 172708
  have htrace : WordTrace (prefixWord ++ tailWord_172708) baseStart_172708 baseEnd_172708 := by
    simpa [prefixWord, tailWord_172708, baseEnd_172708] using wordTrace_append hprefix tailTrace_172708
  have hstable : (prefixWord ++ tailWord_172708).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172708).length < 2 ^ (prefixWord ++ tailWord_172708).sum := by decide
  have hdescent : baseEnd_172708 < baseStart_172708 := by decide
  rcases family_descends (prefixWord ++ tailWord_172708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172723 : List Nat := [1, 1, 1, 2, 3, 4, 4, 2, 4]
def baseStart_172723 : Nat := 118140960795 + 172723 * 2 ^ 59
def prefixEnd_172723 : Nat := 4983230072969 + 3 ^ 40 * 172723 * 2
def baseEnd_172723 : Nat := 19708870908140656481815

theorem tailTrace_172723 : CollatzResearch.WordTrace tailWord_172723 prefixEnd_172723 19708870908140656481815 := by
  unfold tailWord_172723
  simp only [CollatzResearch.WordTrace]
  refine ⟨6299725353261544584994823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4199816902174363056663215 6299725353261544584994823)
  ·
    refine ⟨9449588029892316877492235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6299725353261544584994823 9449588029892316877492235)
    ·
      refine ⟨14174382044838475316238353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9449588029892316877492235 14174382044838475316238353)
      ·
        refine ⟨10630786533628856487178765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14174382044838475316238353 10630786533628856487178765)
        ·
          refine ⟨3986544950110821182692037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10630786533628856487178765 3986544950110821182692037)
          ·
            refine ⟨747477178145778971754757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3986544950110821182692037 747477178145778971754757)
            ·
              refine ⟨140151970902333557204017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 747477178145778971754757 140151970902333557204017)
              ·
                refine ⟨105113978176750167903013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 140151970902333557204017 105113978176750167903013)
                ·
                  refine ⟨19708870908140656481815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 105113978176750167903013 19708870908140656481815)
                  ·
                    rfl

theorem cell22_172723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 4, 2, 4].length) (baseStart_172723 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_172723 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_172723 prefixEnd_172723 := by exact prefixLift 172723
  have htrace : WordTrace (prefixWord ++ tailWord_172723) baseStart_172723 baseEnd_172723 := by
    simpa [prefixWord, tailWord_172723, baseEnd_172723] using wordTrace_append hprefix tailTrace_172723
  have hstable : (prefixWord ++ tailWord_172723).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172723).length < 2 ^ (prefixWord ++ tailWord_172723).sum := by decide
  have hdescent : baseEnd_172723 < baseStart_172723 := by decide
  rcases family_descends (prefixWord ++ tailWord_172723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172783 : List Nat := [1, 1, 2, 1, 5, 3, 2, 1, 3, 3]
def baseStart_172783 : Nat := 118140960795 + 172783 * 2 ^ 59
def prefixEnd_172783 : Nat := 4983230072969 + 3 ^ 40 * 172783 * 2
def baseEnd_172783 : Nat := 59147151950601812945261

theorem tailTrace_172783 : CollatzResearch.WordTrace tailWord_172783 prefixEnd_172783 59147151950601812945261 := by
  unfold tailWord_172783
  simp only [CollatzResearch.WordTrace]
  refine ⟨6301913733044174832179003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4201275822029449888119335 6301913733044174832179003)
  ·
    refine ⟨9452870599566262248268505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6301913733044174832179003 9452870599566262248268505)
    ·
      refine ⟨7089652949674696686201379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9452870599566262248268505 7089652949674696686201379)
      ·
        refine ⟨10634479424512045029302069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7089652949674696686201379 10634479424512045029302069)
        ·
          refine ⟨996982446048004221497069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10634479424512045029302069 996982446048004221497069)
          ·
            refine ⟨373868417268001583061401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 996982446048004221497069 373868417268001583061401)
            ·
              refine ⟨280401312951001187296051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 373868417268001583061401 280401312951001187296051)
              ·
                refine ⟨420601969426501780944077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 280401312951001187296051 420601969426501780944077)
                ·
                  refine ⟨157725738534938167854029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 420601969426501780944077 157725738534938167854029)
                  ·
                    refine ⟨59147151950601812945261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 157725738534938167854029 59147151950601812945261)
                    ·
                      rfl

theorem cell22_172783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 2, 1, 3, 3].length) (baseStart_172783 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_172783 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_172783 prefixEnd_172783 := by exact prefixLift 172783
  have htrace : WordTrace (prefixWord ++ tailWord_172783) baseStart_172783 baseEnd_172783 := by
    simpa [prefixWord, tailWord_172783, baseEnd_172783] using wordTrace_append hprefix tailTrace_172783
  have hstable : (prefixWord ++ tailWord_172783).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172783).length < 2 ^ (prefixWord ++ tailWord_172783).sum := by decide
  have hdescent : baseEnd_172783 < baseStart_172783 := by decide
  rcases family_descends (prefixWord ++ tailWord_172783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172789 : List Nat := [1, 3, 6, 1, 2, 1, 1, 1, 1, 5]
def baseStart_172789 : Nat := 118140960795 + 172789 * 2 ^ 59
def prefixEnd_172789 : Nat := 4983230072969 + 3 ^ 40 * 172789 * 2
def baseEnd_172789 : Nat := 59149205873219797295243

theorem tailTrace_172789 : CollatzResearch.WordTrace tailWord_172789 prefixEnd_172789 59149205873219797295243 := by
  unfold tailWord_172789
  simp only [CollatzResearch.WordTrace]
  refine ⟨6302132571022437856897421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4201421714014958571264947 6302132571022437856897421)
  ·
    refine ⟨2363299714133414196336533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6302132571022437856897421 2363299714133414196336533)
    ·
      refine ⟨110779674100003790453275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 2363299714133414196336533 110779674100003790453275)
      ·
        refine ⟨166169511150005685679913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110779674100003790453275 166169511150005685679913)
        ·
          refine ⟨124627133362504264259935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 166169511150005685679913 124627133362504264259935)
          ·
            refine ⟨186940700043756396389903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124627133362504264259935 186940700043756396389903)
            ·
              refine ⟨280411050065634594584855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 186940700043756396389903 280411050065634594584855)
              ·
                refine ⟨420616575098451891877283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 280411050065634594584855 420616575098451891877283)
                ·
                  refine ⟨630924862647677837815925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 420616575098451891877283 630924862647677837815925)
                  ·
                    refine ⟨59149205873219797295243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 630924862647677837815925 59149205873219797295243)
                    ·
                      rfl

theorem cell22_172789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 1, 1, 1, 5].length) (baseStart_172789 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_172789 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_172789 prefixEnd_172789 := by exact prefixLift 172789
  have htrace : WordTrace (prefixWord ++ tailWord_172789) baseStart_172789 baseEnd_172789 := by
    simpa [prefixWord, tailWord_172789, baseEnd_172789] using wordTrace_append hprefix tailTrace_172789
  have hstable : (prefixWord ++ tailWord_172789).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172789).length < 2 ^ (prefixWord ++ tailWord_172789).sum := by decide
  have hdescent : baseEnd_172789 < baseStart_172789 := by decide
  rcases family_descends (prefixWord ++ tailWord_172789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172856 : List Nat := [2, 1, 2, 1, 3, 2, 2, 3, 1, 5]
def baseStart_172856 : Nat := 118140960795 + 172856 * 2 ^ 59
def prefixEnd_172856 : Nat := 4983230072969 + 3 ^ 40 * 172856 * 2
def baseEnd_172856 : Nat := 59172141342453955870037

theorem tailTrace_172856 : CollatzResearch.WordTrace tailWord_172856 prefixEnd_172856 59172141342453955870037 := by
  unfold tailWord_172856
  simp only [CollatzResearch.WordTrace]
  refine ⟨3152288130889854149793211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4203050841186472199724281 3152288130889854149793211)
  ·
    refine ⟨4728432196334781224689817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3152288130889854149793211 4728432196334781224689817)
    ·
      refine ⟨3546324147251085918517363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4728432196334781224689817 3546324147251085918517363)
      ·
        refine ⟨5319486220876628877776045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3546324147251085918517363 5319486220876628877776045)
        ·
          refine ⟨1994807332828735829166017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5319486220876628877776045 1994807332828735829166017)
          ·
            refine ⟨1496105499621551871874513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1994807332828735829166017 1496105499621551871874513)
            ·
              refine ⟨1122079124716163903905885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1496105499621551871874513 1122079124716163903905885)
              ·
                refine ⟨420779671768561463964707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1122079124716163903905885 420779671768561463964707)
                ·
                  refine ⟨631169507652842195947061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 420779671768561463964707 631169507652842195947061)
                  ·
                    refine ⟨59172141342453955870037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 631169507652842195947061 59172141342453955870037)
                    ·
                      rfl

theorem cell22_172856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 3, 1, 5].length) (baseStart_172856 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_172856 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_172856 prefixEnd_172856 := by exact prefixLift 172856
  have htrace : WordTrace (prefixWord ++ tailWord_172856) baseStart_172856 baseEnd_172856 := by
    simpa [prefixWord, tailWord_172856, baseEnd_172856] using wordTrace_append hprefix tailTrace_172856
  have hstable : (prefixWord ++ tailWord_172856).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172856).length < 2 ^ (prefixWord ++ tailWord_172856).sum := by decide
  have hdescent : baseEnd_172856 < baseStart_172856 := by decide
  rcases family_descends (prefixWord ++ tailWord_172856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172886 : List Nat := [5, 2, 15]
def baseStart_172886 : Nat := 118140960795 + 172886 * 2 ^ 59
def prefixEnd_172886 : Nat := 4983230072969 + 3 ^ 40 * 172886 * 2
def baseEnd_172886 : Nat := 27061001808662038235

theorem tailTrace_172886 : CollatzResearch.WordTrace tailWord_172886 prefixEnd_172886 27061001808662038235 := by
  unfold tailWord_172886
  simp only [CollatzResearch.WordTrace]
  refine ⟨394104403229438963948657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4203780301114015615452341 394104403229438963948657)
  ·
    refine ⟨295578302422079222961493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 394104403229438963948657 295578302422079222961493)
    ·
      refine ⟨27061001808662038235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 15 295578302422079222961493 27061001808662038235)
      ·
        rfl

theorem cell22_172886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 15].length) (baseStart_172886 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_172886 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_172886 prefixEnd_172886 := by exact prefixLift 172886
  have htrace : WordTrace (prefixWord ++ tailWord_172886) baseStart_172886 baseEnd_172886 := by
    simpa [prefixWord, tailWord_172886, baseEnd_172886] using wordTrace_append hprefix tailTrace_172886
  have hstable : (prefixWord ++ tailWord_172886).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172886).length < 2 ^ (prefixWord ++ tailWord_172886).sum := by decide
  have hdescent : baseEnd_172886 < baseStart_172886 := by decide
  rcases family_descends (prefixWord ++ tailWord_172886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172890 : List Nat := [3, 1, 1, 2, 1, 5, 2, 2, 2, 3]
def baseStart_172890 : Nat := 118140960795 + 172890 * 2 ^ 59
def prefixEnd_172890 : Nat := 4983230072969 + 3 ^ 40 * 172890 * 2
def baseEnd_172890 : Nat := 59183780237289200519933

theorem tailTrace_172890 : CollatzResearch.WordTrace tailWord_172890 prefixEnd_172890 59183780237289200519933 := by
  unfold tailWord_172890
  simp only [CollatzResearch.WordTrace]
  refine ⟨1576454085914133026581031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4203877562437688070882749 1576454085914133026581031)
  ·
    refine ⟨2364681128871199539871547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1576454085914133026581031 2364681128871199539871547)
    ·
      refine ⟨3547021693306799309807321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2364681128871199539871547 3547021693306799309807321)
      ·
        refine ⟨2660266269980099482355491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3547021693306799309807321 2660266269980099482355491)
        ·
          refine ⟨3990399404970149223533237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2660266269980099482355491 3990399404970149223533237)
          ·
            refine ⟨374099944215951489706241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3990399404970149223533237 374099944215951489706241)
            ·
              refine ⟨280574958161963617279681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 374099944215951489706241 280574958161963617279681)
              ·
                refine ⟨210431218621472712959761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 280574958161963617279681 210431218621472712959761)
                ·
                  refine ⟨157823413966104534719821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 210431218621472712959761 157823413966104534719821)
                  ·
                    refine ⟨59183780237289200519933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 157823413966104534719821 59183780237289200519933)
                    ·
                      rfl

theorem cell22_172890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 2, 2, 2, 3].length) (baseStart_172890 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_172890 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_172890 prefixEnd_172890 := by exact prefixLift 172890
  have htrace : WordTrace (prefixWord ++ tailWord_172890) baseStart_172890 baseEnd_172890 := by
    simpa [prefixWord, tailWord_172890, baseEnd_172890] using wordTrace_append hprefix tailTrace_172890
  have hstable : (prefixWord ++ tailWord_172890).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172890).length < 2 ^ (prefixWord ++ tailWord_172890).sum := by decide
  have hdescent : baseEnd_172890 < baseStart_172890 := by decide
  rcases family_descends (prefixWord ++ tailWord_172890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172892 : List Nat := [2, 2, 4, 2, 1, 1, 4, 2, 4]
def baseStart_172892 : Nat := 118140960795 + 172892 * 2 ^ 59
def prefixEnd_172892 : Nat := 4983230072969 + 3 ^ 40 * 172892 * 2
def baseEnd_172892 : Nat := 19728154959387287323309

theorem tailTrace_172892 : CollatzResearch.WordTrace tailWord_172892 prefixEnd_172892 19728154959387287323309 := by
  unfold tailWord_172892
  simp only [CollatzResearch.WordTrace]
  refine ⟨3152944644824643223948465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4203926193099524298597953 3152944644824643223948465)
  ·
    refine ⟨2364708483618482417961349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3152944644824643223948465 2364708483618482417961349)
    ·
      refine ⟨443382840678465453367753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2364708483618482417961349 443382840678465453367753)
      ·
        refine ⟨332537130508849090025815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 443382840678465453367753 332537130508849090025815)
        ·
          refine ⟨498805695763273635038723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 332537130508849090025815 498805695763273635038723)
          ·
            refine ⟨748208543644910452558085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 498805695763273635038723 748208543644910452558085)
            ·
              refine ⟨140289101933420709854641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 748208543644910452558085 140289101933420709854641)
              ·
                refine ⟨105216826450065532390981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 140289101933420709854641 105216826450065532390981)
                ·
                  refine ⟨19728154959387287323309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 105216826450065532390981 19728154959387287323309)
                  ·
                    rfl

theorem cell22_172892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 4, 2, 4].length) (baseStart_172892 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_172892 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_172892 prefixEnd_172892 := by exact prefixLift 172892
  have htrace : WordTrace (prefixWord ++ tailWord_172892) baseStart_172892 baseEnd_172892 := by
    simpa [prefixWord, tailWord_172892, baseEnd_172892] using wordTrace_append hprefix tailTrace_172892
  have hstable : (prefixWord ++ tailWord_172892).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172892).length < 2 ^ (prefixWord ++ tailWord_172892).sum := by decide
  have hdescent : baseEnd_172892 < baseStart_172892 := by decide
  rcases family_descends (prefixWord ++ tailWord_172892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172903 : List Nat := [1, 1, 5, 1, 2, 4, 1, 7]
def baseStart_172903 : Nat := 118140960795 + 172903 * 2 ^ 59
def prefixEnd_172903 : Nat := 4983230072969 + 3 ^ 40 * 172903 * 2
def baseEnd_172903 : Nat := 6576470044773499993877

theorem tailTrace_172903 : CollatzResearch.WordTrace tailWord_172903 prefixEnd_172903 6576470044773499993877 := by
  unfold tailWord_172903
  simp only [CollatzResearch.WordTrace]
  refine ⟨6306290492609435326547363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4204193661739623551031575 6306290492609435326547363)
  ·
    refine ⟨9459435738914152989821045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6306290492609435326547363 9459435738914152989821045)
    ·
      refine ⟨886822100523201842795723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9459435738914152989821045 886822100523201842795723)
      ·
        refine ⟨1330233150784802764193585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 886822100523201842795723 1330233150784802764193585)
        ·
          refine ⟨997674863088602073145189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1330233150784802764193585 997674863088602073145189)
          ·
            refine ⟨187064036829112888714723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 997674863088602073145189 187064036829112888714723)
            ·
              refine ⟨280596055243669333072085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 187064036829112888714723 280596055243669333072085)
              ·
                refine ⟨6576470044773499993877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 280596055243669333072085 6576470044773499993877)
                ·
                  rfl

theorem cell22_172903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 1, 7].length) (baseStart_172903 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_172903 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_172903 prefixEnd_172903 := by exact prefixLift 172903
  have htrace : WordTrace (prefixWord ++ tailWord_172903) baseStart_172903 baseEnd_172903 := by
    simpa [prefixWord, tailWord_172903, baseEnd_172903] using wordTrace_append hprefix tailTrace_172903
  have hstable : (prefixWord ++ tailWord_172903).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172903).length < 2 ^ (prefixWord ++ tailWord_172903).sum := by decide
  have hdescent : baseEnd_172903 < baseStart_172903 := by decide
  rcases family_descends (prefixWord ++ tailWord_172903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172931 : List Nat := [1, 1, 1, 3, 4, 1, 2, 2, 7]
def baseStart_172931 : Nat := 118140960795 + 172931 * 2 ^ 59
def prefixEnd_172931 : Nat := 4983230072969 + 3 ^ 40 * 172931 * 2
def baseEnd_172931 : Nat := 19732605125059586748269

theorem tailTrace_172931 : CollatzResearch.WordTrace tailWord_172931 prefixEnd_172931 19732605125059586748269 := by
  unfold tailWord_172931
  simp only [CollatzResearch.WordTrace]
  refine ⟨6307311736507996108566647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4204874491005330739044431 6307311736507996108566647)
  ·
    refine ⟨9460967604761994162849971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6307311736507996108566647 9460967604761994162849971)
    ·
      refine ⟨14191451407142991244274957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9460967604761994162849971 14191451407142991244274957)
      ·
        refine ⟨5321794277678621716603109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14191451407142991244274957 5321794277678621716603109)
        ·
          refine ⟨997836427064741571863083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5321794277678621716603109 997836427064741571863083)
          ·
            refine ⟨1496754640597112357794625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 997836427064741571863083 1496754640597112357794625)
            ·
              refine ⟨1122565980447834268345969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1496754640597112357794625 1122565980447834268345969)
              ·
                refine ⟨841924485335875701259477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1122565980447834268345969 841924485335875701259477)
                ·
                  refine ⟨19732605125059586748269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 841924485335875701259477 19732605125059586748269)
                  ·
                    rfl

theorem cell22_172931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 2, 7].length) (baseStart_172931 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_172931 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_172931 prefixEnd_172931 := by exact prefixLift 172931
  have htrace : WordTrace (prefixWord ++ tailWord_172931) baseStart_172931 baseEnd_172931 := by
    simpa [prefixWord, tailWord_172931, baseEnd_172931] using wordTrace_append hprefix tailTrace_172931
  have hstable : (prefixWord ++ tailWord_172931).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172931).length < 2 ^ (prefixWord ++ tailWord_172931).sum := by decide
  have hdescent : baseEnd_172931 < baseStart_172931 := by decide
  rcases family_descends (prefixWord ++ tailWord_172931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172948 : List Nat := [2, 4, 2, 1, 1, 1, 3, 1, 7]
def baseStart_172948 : Nat := 118140960795 + 172948 * 2 ^ 59
def prefixEnd_172948 : Nat := 4983230072969 + 3 ^ 40 * 172948 * 2
def baseEnd_172948 : Nat := 19734544940865460856585

theorem tailTrace_172948 : CollatzResearch.WordTrace tailWord_172948 prefixEnd_172948 19734544940865460856585 := by
  unfold tailWord_172948
  simp only [CollatzResearch.WordTrace]
  refine ⟨3153965888723204005967749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4205287851630938674623665 3153965888723204005967749)
  ·
    refine ⟨591368604135600751118953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3153965888723204005967749 591368604135600751118953)
    ·
      refine ⟨443526453101700563339215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 591368604135600751118953 443526453101700563339215)
      ·
        refine ⟨665289679652550845008823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 443526453101700563339215 665289679652550845008823)
        ·
          refine ⟨997934519478826267513235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 665289679652550845008823 997934519478826267513235)
          ·
            refine ⟨1496901779218239401269853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 997934519478826267513235 1496901779218239401269853)
            ·
              refine ⟨561338167206839775476195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1496901779218239401269853 561338167206839775476195)
              ·
                refine ⟨842007250810259663214293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 561338167206839775476195 842007250810259663214293)
                ·
                  refine ⟨19734544940865460856585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 842007250810259663214293 19734544940865460856585)
                  ·
                    rfl

theorem cell22_172948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 3, 1, 7].length) (baseStart_172948 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_172948 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_172948 prefixEnd_172948 := by exact prefixLift 172948
  have htrace : WordTrace (prefixWord ++ tailWord_172948) baseStart_172948 baseEnd_172948 := by
    simpa [prefixWord, tailWord_172948, baseEnd_172948] using wordTrace_append hprefix tailTrace_172948
  have hstable : (prefixWord ++ tailWord_172948).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172948).length < 2 ^ (prefixWord ++ tailWord_172948).sum := by decide
  have hdescent : baseEnd_172948 < baseStart_172948 := by decide
  rcases family_descends (prefixWord ++ tailWord_172948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173010 : List Nat := [3, 2, 2, 3, 1, 1, 3, 1, 6]
def baseStart_173010 : Nat := 118140960795 + 173010 * 2 ^ 59
def prefixEnd_173010 : Nat := 4983230072969 + 3 ^ 40 * 173010 * 2
def baseEnd_173010 : Nat := 19741619563216295839855

theorem tailTrace_173010 : CollatzResearch.WordTrace tailWord_173010 prefixEnd_173010 19741619563216295839855 := by
  unfold tailWord_173010
  simp only [CollatzResearch.WordTrace]
  refine ⟨1577548275805448150173121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4206795402147861733794989 1577548275805448150173121)
  ·
    refine ⟨1183161206854086112629841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1577548275805448150173121 1183161206854086112629841)
    ·
      refine ⟨887370905140564584472381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1183161206854086112629841 887370905140564584472381)
      ·
        refine ⟨332764089427711719177143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 887370905140564584472381 332764089427711719177143)
        ·
          refine ⟨499146134141567578765715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 332764089427711719177143 499146134141567578765715)
          ·
            refine ⟨748719201212351368148573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 499146134141567578765715 748719201212351368148573)
            ·
              refine ⟨280769700454631763055715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 748719201212351368148573 280769700454631763055715)
              ·
                refine ⟨421154550681947644583573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 280769700454631763055715 421154550681947644583573)
                ·
                  refine ⟨19741619563216295839855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 421154550681947644583573 19741619563216295839855)
                  ·
                    rfl

theorem cell22_173010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 3, 1, 6].length) (baseStart_173010 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_173010 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_173010 prefixEnd_173010 := by exact prefixLift 173010
  have htrace : WordTrace (prefixWord ++ tailWord_173010) baseStart_173010 baseEnd_173010 := by
    simpa [prefixWord, tailWord_173010, baseEnd_173010] using wordTrace_append hprefix tailTrace_173010
  have hstable : (prefixWord ++ tailWord_173010).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173010).length < 2 ^ (prefixWord ++ tailWord_173010).sum := by decide
  have hdescent : baseEnd_173010 < baseStart_173010 := by decide
  rcases family_descends (prefixWord ++ tailWord_173010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173029 : List Nat := [1, 3, 1, 6, 1, 2, 1, 2, 1, 4]
def baseStart_173029 : Nat := 118140960795 + 173029 * 2 ^ 59
def prefixEnd_173029 : Nat := 4983230072969 + 3 ^ 40 * 173029 * 2
def baseEnd_173029 : Nat := 59231362777939171294507

theorem tailTrace_173029 : CollatzResearch.WordTrace tailWord_173029 prefixEnd_173029 59231362777939171294507 := by
  unfold tailWord_173029
  simp only [CollatzResearch.WordTrace]
  refine ⟨6310886090152958845634141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4207257393435305897089427 6310886090152958845634141)
  ·
    refine ⟨2366582283807359567112803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6310886090152958845634141 2366582283807359567112803)
    ·
      refine ⟨3549873425711039350669205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2366582283807359567112803 3549873425711039350669205)
      ·
        refine ⟨166400316830204969562619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 3549873425711039350669205 166400316830204969562619)
        ·
          refine ⟨249600475245307454343929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 166400316830204969562619 249600475245307454343929)
          ·
            refine ⟨187200356433980590757947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 249600475245307454343929 187200356433980590757947)
            ·
              refine ⟨280800534650970886136921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 187200356433980590757947 280800534650970886136921)
              ·
                refine ⟨210600400988228164602691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 280800534650970886136921 210600400988228164602691)
                ·
                  refine ⟨315900601482342246904037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 210600400988228164602691 315900601482342246904037)
                  ·
                    refine ⟨59231362777939171294507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 315900601482342246904037 59231362777939171294507)
                    ·
                      rfl

theorem cell22_173029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 1, 2, 1, 4].length) (baseStart_173029 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_173029 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_173029 prefixEnd_173029 := by exact prefixLift 173029
  have htrace : WordTrace (prefixWord ++ tailWord_173029) baseStart_173029 baseEnd_173029 := by
    simpa [prefixWord, tailWord_173029, baseEnd_173029] using wordTrace_append hprefix tailTrace_173029
  have hstable : (prefixWord ++ tailWord_173029).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173029).length < 2 ^ (prefixWord ++ tailWord_173029).sum := by decide
  have hdescent : baseEnd_173029 < baseStart_173029 := by decide
  rcases family_descends (prefixWord ++ tailWord_173029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173042 : List Nat := [3, 2, 1, 5, 1, 1, 1, 2, 1, 5]
def baseStart_173042 : Nat := 118140960795 + 173042 * 2 ^ 59
def prefixEnd_173042 : Nat := 4983230072969 + 3 ^ 40 * 173042 * 2
def baseEnd_173042 : Nat := 59235812943611470719467

theorem tailTrace_173042 : CollatzResearch.WordTrace tailWord_173042 prefixEnd_173042 59235812943611470719467 := by
  unfold tailWord_173042
  simp only [CollatzResearch.WordTrace]
  refine ⟨1577840059776465516464345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4207573492737241377238253 1577840059776465516464345)
  ·
    refine ⟨1183380044832349137348259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1577840059776465516464345 1183380044832349137348259)
    ·
      refine ⟨1775070067248523706022389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1183380044832349137348259 1775070067248523706022389)
      ·
        refine ⟨166412818804549097439599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1775070067248523706022389 166412818804549097439599)
        ·
          refine ⟨249619228206823646159399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 166412818804549097439599 249619228206823646159399)
          ·
            refine ⟨374428842310235469239099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 249619228206823646159399 374428842310235469239099)
            ·
              refine ⟨561643263465353203858649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 374428842310235469239099 561643263465353203858649)
              ·
                refine ⟨421232447599014902893987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 561643263465353203858649 421232447599014902893987)
                ·
                  refine ⟨631848671398522354340981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 421232447599014902893987 631848671398522354340981)
                  ·
                    refine ⟨59235812943611470719467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 631848671398522354340981 59235812943611470719467)
                    ·
                      rfl

theorem cell22_173042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 1, 2, 1, 5].length) (baseStart_173042 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_173042 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_173042 prefixEnd_173042 := by exact prefixLift 173042
  have htrace : WordTrace (prefixWord ++ tailWord_173042) baseStart_173042 baseEnd_173042 := by
    simpa [prefixWord, tailWord_173042, baseEnd_173042] using wordTrace_append hprefix tailTrace_173042
  have hstable : (prefixWord ++ tailWord_173042).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173042).length < 2 ^ (prefixWord ++ tailWord_173042).sum := by decide
  have hdescent : baseEnd_173042 < baseStart_173042 := by decide
  rcases family_descends (prefixWord ++ tailWord_173042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173068 : List Nat := [2, 2, 1, 2, 3, 2, 1, 1, 2, 6]
def baseStart_173068 : Nat := 118140960795 + 173068 * 2 ^ 59
def prefixEnd_173068 : Nat := 4983230072969 + 3 ^ 40 * 173068 * 2
def baseEnd_173068 : Nat := 59244713274956069569387

theorem tailTrace_173068 : CollatzResearch.WordTrace tailWord_173068 prefixEnd_173068 59244713274956069569387 := by
  unfold tailWord_173068
  simp only [CollatzResearch.WordTrace]
  refine ⟨3156154268505834253151929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4208205691341112337535905 3156154268505834253151929)
  ·
    refine ⟨2367115701379375689863947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3156154268505834253151929 2367115701379375689863947)
    ·
      refine ⟨3550673552069063534795921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2367115701379375689863947 3550673552069063534795921)
      ·
        refine ⟨2663005164051797651096941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3550673552069063534795921 2663005164051797651096941)
        ·
          refine ⟨998626936519424119161353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2663005164051797651096941 998626936519424119161353)
          ·
            refine ⟨748970202389568089371015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 998626936519424119161353 748970202389568089371015)
            ·
              refine ⟨1123455303584352134056523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 748970202389568089371015 1123455303584352134056523)
              ·
                refine ⟨1685182955376528201084785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1123455303584352134056523 1685182955376528201084785)
                ·
                  refine ⟨1263887216532396150813589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1685182955376528201084785 1263887216532396150813589)
                  ·
                    refine ⟨59244713274956069569387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1263887216532396150813589 59244713274956069569387)
                    ·
                      rfl

theorem cell22_173068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 1, 2, 6].length) (baseStart_173068 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_173068 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_173068 prefixEnd_173068 := by exact prefixLift 173068
  have htrace : WordTrace (prefixWord ++ tailWord_173068) baseStart_173068 baseEnd_173068 := by
    simpa [prefixWord, tailWord_173068, baseEnd_173068] using wordTrace_append hprefix tailTrace_173068
  have hstable : (prefixWord ++ tailWord_173068).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173068).length < 2 ^ (prefixWord ++ tailWord_173068).sum := by decide
  have hdescent : baseEnd_173068 < baseStart_173068 := by decide
  rcases family_descends (prefixWord ++ tailWord_173068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173117 : List Nat := [1, 4, 1, 3, 1, 4, 1, 2, 5]
def baseStart_173117 : Nat := 118140960795 + 173117 * 2 ^ 59
def prefixEnd_173117 : Nat := 4983230072969 + 3 ^ 40 * 173117 * 2
def baseEnd_173117 : Nat := 19753828992112091698079

theorem tailTrace_173117 : CollatzResearch.WordTrace tailWord_173117 prefixEnd_173117 19753828992112091698079 := by
  unfold tailWord_173117
  simp only [CollatzResearch.WordTrace]
  refine ⟨6314095713834149874837605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4209397142556099916558403 6314095713834149874837605)
  ·
    refine ⟨1183892946343903101532051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6314095713834149874837605 1183892946343903101532051)
    ·
      refine ⟨1775839419515854652298077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1183892946343903101532051 1775839419515854652298077)
      ·
        refine ⟨665939782318445494611779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1775839419515854652298077 665939782318445494611779)
        ·
          refine ⟨998909673477668241917669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 665939782318445494611779 998909673477668241917669)
          ·
            refine ⟨187295563777062795359563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 998909673477668241917669 187295563777062795359563)
            ·
              refine ⟨280943345665594193039345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 187295563777062795359563 280943345665594193039345)
              ·
                refine ⟨210707509249195644779509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 280943345665594193039345 210707509249195644779509)
                ·
                  refine ⟨19753828992112091698079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 210707509249195644779509 19753828992112091698079)
                  ·
                    rfl

theorem cell22_173117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 1, 2, 5].length) (baseStart_173117 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_173117 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_173117 prefixEnd_173117 := by exact prefixLift 173117
  have htrace : WordTrace (prefixWord ++ tailWord_173117) baseStart_173117 baseEnd_173117 := by
    simpa [prefixWord, tailWord_173117, baseEnd_173117] using wordTrace_append hprefix tailTrace_173117
  have hstable : (prefixWord ++ tailWord_173117).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173117).length < 2 ^ (prefixWord ++ tailWord_173117).sum := by decide
  have hdescent : baseEnd_173117 < baseStart_173117 := by decide
  rcases family_descends (prefixWord ++ tailWord_173117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173175 : List Nat := [1, 1, 3, 1, 1, 4, 3, 2, 2, 4]
def baseStart_173175 : Nat := 118140960795 + 173175 * 2 ^ 59
def prefixEnd_173175 : Nat := 4983230072969 + 3 ^ 40 * 173175 * 2
def baseEnd_173175 : Nat := 59281341561643457144059

theorem tailTrace_173175 : CollatzResearch.WordTrace tailWord_173175 prefixEnd_173175 59281341561643457144059 := by
  unfold tailWord_173175
  simp only [CollatzResearch.WordTrace]
  refine ⟨6316211147624025780448979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4210807431749350520299319 6316211147624025780448979)
  ·
    refine ⟨9474316721436038670673469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6316211147624025780448979 9474316721436038670673469)
    ·
      refine ⟨3552868770538514501502551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9474316721436038670673469 3552868770538514501502551)
      ·
        refine ⟨5329303155807771752253827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3552868770538514501502551 5329303155807771752253827)
        ·
          refine ⟨7993954733711657628380741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5329303155807771752253827 7993954733711657628380741)
          ·
            refine ⟨1498866512570935805321389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7993954733711657628380741 1498866512570935805321389)
            ·
              refine ⟨562074942214100926995521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1498866512570935805321389 562074942214100926995521)
              ·
                refine ⟨421556206660575695246641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 562074942214100926995521 421556206660575695246641)
                ·
                  refine ⟨316167154995431771434981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 421556206660575695246641 316167154995431771434981)
                  ·
                    refine ⟨59281341561643457144059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 316167154995431771434981 59281341561643457144059)
                    ·
                      rfl

theorem cell22_173175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 3, 2, 2, 4].length) (baseStart_173175 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_173175 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_173175 prefixEnd_173175 := by exact prefixLift 173175
  have htrace : WordTrace (prefixWord ++ tailWord_173175) baseStart_173175 baseEnd_173175 := by
    simpa [prefixWord, tailWord_173175, baseEnd_173175] using wordTrace_append hprefix tailTrace_173175
  have hstable : (prefixWord ++ tailWord_173175).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173175).length < 2 ^ (prefixWord ++ tailWord_173175).sum := by decide
  have hdescent : baseEnd_173175 < baseStart_173175 := by decide
  rcases family_descends (prefixWord ++ tailWord_173175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173235 : List Nat := [1, 1, 1, 2, 3, 2, 3, 4, 5]
def baseStart_173235 : Nat := 118140960795 + 173235 * 2 ^ 59
def prefixEnd_173235 : Nat := 4983230072969 + 3 ^ 40 * 173235 * 2
def baseEnd_173235 : Nat := 19767293595941100214625

theorem tailTrace_173235 : CollatzResearch.WordTrace tailWord_173235 prefixEnd_173235 19767293595941100214625 := by
  unfold tailWord_173235
  simp only [CollatzResearch.WordTrace]
  refine ⟨6318399527406656027633159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4212266351604437351755439 6318399527406656027633159)
  ·
    refine ⟨9477599291109984041449739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6318399527406656027633159 9477599291109984041449739)
    ·
      refine ⟨14216398936664976062174609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9477599291109984041449739 14216398936664976062174609)
      ·
        refine ⟨10662299202498732046630957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14216398936664976062174609 10662299202498732046630957)
        ·
          refine ⟨3998362200937024517486609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10662299202498732046630957 3998362200937024517486609)
          ·
            refine ⟨2998771650702768388114957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3998362200937024517486609 2998771650702768388114957)
            ·
              refine ⟨1124539369013538145543109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2998771650702768388114957 1124539369013538145543109)
              ·
                refine ⟨210851131690038402289333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1124539369013538145543109 210851131690038402289333)
                ·
                  refine ⟨19767293595941100214625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 210851131690038402289333 19767293595941100214625)
                  ·
                    rfl

theorem cell22_173235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 4, 5].length) (baseStart_173235 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_173235 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_173235 prefixEnd_173235 := by exact prefixLift 173235
  have htrace : WordTrace (prefixWord ++ tailWord_173235) baseStart_173235 baseEnd_173235 := by
    simpa [prefixWord, tailWord_173235, baseEnd_173235] using wordTrace_append hprefix tailTrace_173235
  have hstable : (prefixWord ++ tailWord_173235).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173235).length < 2 ^ (prefixWord ++ tailWord_173235).sum := by decide
  have hdescent : baseEnd_173235 < baseStart_173235 := by decide
  rcases family_descends (prefixWord ++ tailWord_173235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173239 : List Nat := [1, 1, 3, 1, 4, 1, 3, 4, 1, 3]
def baseStart_173239 : Nat := 118140960795 + 173239 * 2 ^ 59
def prefixEnd_173239 : Nat := 4983230072969 + 3 ^ 40 * 173239 * 2
def baseEnd_173239 : Nat := 59303250069568623543863

theorem tailTrace_173239 : CollatzResearch.WordTrace tailWord_173239 prefixEnd_173239 59303250069568623543863 := by
  unfold tailWord_173239
  simp only [CollatzResearch.WordTrace]
  refine ⟨6318545419392164710778771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4212363612928109807185847 6318545419392164710778771)
  ·
    refine ⟨9477818129088247066168157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6318545419392164710778771 9477818129088247066168157)
    ·
      refine ⟨3554181798408092649813059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9477818129088247066168157 3554181798408092649813059)
      ·
        refine ⟨5331272697612138974719589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3554181798408092649813059 5331272697612138974719589)
        ·
          refine ⟨999613630802276057759923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5331272697612138974719589 999613630802276057759923)
          ·
            refine ⟨1499420446203414086639885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 999613630802276057759923 1499420446203414086639885)
            ·
              refine ⟨562282667326280282489957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1499420446203414086639885 562282667326280282489957)
              ·
                refine ⟨105428000123677552966867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 562282667326280282489957 105428000123677552966867)
                ·
                  refine ⟨158142000185516329450301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 105428000123677552966867 158142000185516329450301)
                  ·
                    refine ⟨59303250069568623543863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 158142000185516329450301 59303250069568623543863)
                    ·
                      rfl

theorem cell22_173239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 3, 4, 1, 3].length) (baseStart_173239 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_173239 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_173239 prefixEnd_173239 := by exact prefixLift 173239
  have htrace : WordTrace (prefixWord ++ tailWord_173239) baseStart_173239 baseEnd_173239 := by
    simpa [prefixWord, tailWord_173239, baseEnd_173239] using wordTrace_append hprefix tailTrace_173239
  have hstable : (prefixWord ++ tailWord_173239).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173239).length < 2 ^ (prefixWord ++ tailWord_173239).sum := by decide
  have hdescent : baseEnd_173239 < baseStart_173239 := by decide
  rcases family_descends (prefixWord ++ tailWord_173239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173344 : List Nat := [2, 1, 1, 5, 3, 1, 1, 2, 2, 4]
def baseStart_173344 : Nat := 118140960795 + 173344 * 2 ^ 59
def prefixEnd_173344 : Nat := 4983230072969 + 3 ^ 40 * 173344 * 2
def baseEnd_173344 : Nat := 59339193715383349668541

theorem tailTrace_173344 : CollatzResearch.WordTrace tailWord_173344 prefixEnd_173344 59339193715383349668541 := by
  unfold tailWord_173344
  simp only [CollatzResearch.WordTrace]
  refine ⟨3161187542005883821675543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4214916722674511762234057 3161187542005883821675543)
  ·
    refine ⟨4741781313008825732513315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3161187542005883821675543 4741781313008825732513315)
    ·
      refine ⟨7112671969513238598769973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4741781313008825732513315 7112671969513238598769973)
      ·
        refine ⟨666812997141866118634685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7112671969513238598769973 666812997141866118634685)
        ·
          refine ⟨250054873928199794488007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 666812997141866118634685 250054873928199794488007)
          ·
            refine ⟨375082310892299691732011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 250054873928199794488007 375082310892299691732011)
            ·
              refine ⟨562623466338449537598017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 375082310892299691732011 562623466338449537598017)
              ·
                refine ⟨421967599753837153198513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 562623466338449537598017 421967599753837153198513)
                ·
                  refine ⟨316475699815377864898885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 421967599753837153198513 316475699815377864898885)
                  ·
                    refine ⟨59339193715383349668541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 316475699815377864898885 59339193715383349668541)
                    ·
                      rfl

theorem cell22_173344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 1, 2, 2, 4].length) (baseStart_173344 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_173344 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_173344 prefixEnd_173344 := by exact prefixLift 173344
  have htrace : WordTrace (prefixWord ++ tailWord_173344) baseStart_173344 baseEnd_173344 := by
    simpa [prefixWord, tailWord_173344, baseEnd_173344] using wordTrace_append hprefix tailTrace_173344
  have hstable : (prefixWord ++ tailWord_173344).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173344).length < 2 ^ (prefixWord ++ tailWord_173344).sum := by decide
  have hdescent : baseEnd_173344 < baseStart_173344 := by decide
  rcases family_descends (prefixWord ++ tailWord_173344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173374 : List Nat := [4, 2, 1, 2, 1, 1, 2, 1, 5, 3]
def baseStart_173374 : Nat := 118140960795 + 173374 * 2 ^ 59
def prefixEnd_173374 : Nat := 4983230072969 + 3 ^ 40 * 173374 * 2
def baseEnd_173374 : Nat := 59349463328473271418449

theorem tailTrace_173374 : CollatzResearch.WordTrace tailWord_173374 prefixEnd_173374 59349463328473271418449 := by
  unfold tailWord_173374
  simp only [CollatzResearch.WordTrace]
  refine ⟨790433659237885345867897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4215646182602055177962117 790433659237885345867897)
  ·
    refine ⟨592825244428414009400923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 790433659237885345867897 592825244428414009400923)
    ·
      refine ⟨889237866642621014101385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 592825244428414009400923 889237866642621014101385)
      ·
        refine ⟨666928399981965760576039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 889237866642621014101385 666928399981965760576039)
        ·
          refine ⟨1000392599972948640864059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 666928399981965760576039 1000392599972948640864059)
          ·
            refine ⟨1500588899959422961296089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1000392599972948640864059 1500588899959422961296089)
            ·
              refine ⟨1125441674969567220972067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1500588899959422961296089 1125441674969567220972067)
              ·
                refine ⟨1688162512454350831458101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1125441674969567220972067 1688162512454350831458101)
                ·
                  refine ⟨158265235542595390449197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1688162512454350831458101 158265235542595390449197)
                  ·
                    refine ⟨59349463328473271418449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 158265235542595390449197 59349463328473271418449)
                    ·
                      rfl

theorem cell22_173374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 1, 5, 3].length) (baseStart_173374 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_173374 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_173374 prefixEnd_173374 := by exact prefixLift 173374
  have htrace : WordTrace (prefixWord ++ tailWord_173374) baseStart_173374 baseEnd_173374 := by
    simpa [prefixWord, tailWord_173374, baseEnd_173374] using wordTrace_append hprefix tailTrace_173374
  have hstable : (prefixWord ++ tailWord_173374).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173374).length < 2 ^ (prefixWord ++ tailWord_173374).sum := by decide
  have hdescent : baseEnd_173374 < baseStart_173374 := by decide
  rcases family_descends (prefixWord ++ tailWord_173374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173408 : List Nat := [2, 1, 1, 3, 4, 1, 4, 2, 1, 3]
def baseStart_173408 : Nat := 118140960795 + 173408 * 2 ^ 59
def prefixEnd_173408 : Nat := 4983230072969 + 3 ^ 40 * 173408 * 2
def baseEnd_173408 : Nat := 59361102223308516068345

theorem tailTrace_173408 : CollatzResearch.WordTrace tailWord_173408 prefixEnd_173408 59361102223308516068345 := by
  unfold tailWord_173408
  simp only [CollatzResearch.WordTrace]
  refine ⟨3162354677889953286840439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4216472903853271049120585 3162354677889953286840439)
  ·
    refine ⟨4743532016834929930260659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3162354677889953286840439 4743532016834929930260659)
    ·
      refine ⟨7115298025252394895390989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4743532016834929930260659 7115298025252394895390989)
      ·
        refine ⟨2668236759469648085771621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7115298025252394895390989 2668236759469648085771621)
        ·
          refine ⟨500294392400559016082179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2668236759469648085771621 500294392400559016082179)
          ·
            refine ⟨750441588600838524123269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 500294392400559016082179 750441588600838524123269)
            ·
              refine ⟨140707797862657223273113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 750441588600838524123269 140707797862657223273113)
              ·
                refine ⟨105530848396992917454835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 140707797862657223273113 105530848396992917454835)
                ·
                  refine ⟨158296272595489376182253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 105530848396992917454835 158296272595489376182253)
                  ·
                    refine ⟨59361102223308516068345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 158296272595489376182253 59361102223308516068345)
                    ·
                      rfl

theorem cell22_173408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 4, 2, 1, 3].length) (baseStart_173408 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_173408 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_173408 prefixEnd_173408 := by exact prefixLift 173408
  have htrace : WordTrace (prefixWord ++ tailWord_173408) baseStart_173408 baseEnd_173408 := by
    simpa [prefixWord, tailWord_173408, baseEnd_173408] using wordTrace_append hprefix tailTrace_173408
  have hstable : (prefixWord ++ tailWord_173408).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173408).length < 2 ^ (prefixWord ++ tailWord_173408).sum := by decide
  have hdescent : baseEnd_173408 < baseStart_173408 := by decide
  rcases family_descends (prefixWord ++ tailWord_173408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173500 : List Nat := [2, 2, 2, 4, 3, 1, 1, 3, 4]
def baseStart_173500 : Nat := 118140960795 + 173500 * 2 ^ 59
def prefixEnd_173500 : Nat := 4983230072969 + 3 ^ 40 * 173500 * 2
def baseEnd_173500 : Nat := 19797531901150314256021

theorem tailTrace_173500 : CollatzResearch.WordTrace tailWord_173500 prefixEnd_173500 19797531901150314256021 := by
  unfold tailWord_173500
  simp only [CollatzResearch.WordTrace]
  refine ⟨3164032435723303143014977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4218709914297737524019969 3164032435723303143014977)
  ·
    refine ⟨2373024326792477357261233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3164032435723303143014977 2373024326792477357261233)
    ·
      refine ⟨1779768245094358017945925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2373024326792477357261233 1779768245094358017945925)
      ·
        refine ⟨333706545955192128364861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1779768245094358017945925 333706545955192128364861)
        ·
          refine ⟨125139954733197048136823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 333706545955192128364861 125139954733197048136823)
          ·
            refine ⟨187709932099795572205235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125139954733197048136823 187709932099795572205235)
            ·
              refine ⟨281564898149693358307853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 187709932099795572205235 281564898149693358307853)
              ·
                refine ⟨105586836806135009365445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 281564898149693358307853 105586836806135009365445)
                ·
                  refine ⟨19797531901150314256021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 105586836806135009365445 19797531901150314256021)
                  ·
                    rfl

theorem cell22_173500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 1, 3, 4].length) (baseStart_173500 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_173500 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_173500 prefixEnd_173500 := by exact prefixLift 173500
  have htrace : WordTrace (prefixWord ++ tailWord_173500) baseStart_173500 baseEnd_173500 := by
    simpa [prefixWord, tailWord_173500, baseEnd_173500] using wordTrace_append hprefix tailTrace_173500
  have hstable : (prefixWord ++ tailWord_173500).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173500).length < 2 ^ (prefixWord ++ tailWord_173500).sum := by decide
  have hdescent : baseEnd_173500 < baseStart_173500 := by decide
  rcases family_descends (prefixWord ++ tailWord_173500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173567 : List Nat := [1, 1, 2, 2, 1, 2, 2, 1, 10]
def baseStart_173567 : Nat := 118140960795 + 173567 * 2 ^ 59
def prefixEnd_173567 : Nat := 4983230072969 + 3 ^ 40 * 173567 * 2
def baseEnd_173567 : Nat := 19805177057561700447619

theorem tailTrace_173567 : CollatzResearch.WordTrace tailWord_173567 prefixEnd_173567 19805177057561700447619 := by
  unfold tailWord_173567
  simp only [CollatzResearch.WordTrace]
  refine ⟨6330508562203876728718955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4220339041469251152479303 6330508562203876728718955)
  ·
    refine ⟨9495762843305815093078433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6330508562203876728718955 9495762843305815093078433)
    ·
      refine ⟨7121822132479361319808825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9495762843305815093078433 7121822132479361319808825)
      ·
        refine ⟨5341366599359520989856619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7121822132479361319808825 5341366599359520989856619)
        ·
          refine ⟨8012049899039281484784929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5341366599359520989856619 8012049899039281484784929)
          ·
            refine ⟨6009037424279461113588697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8012049899039281484784929 6009037424279461113588697)
            ·
              refine ⟨4506778068209595835191523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6009037424279461113588697 4506778068209595835191523)
              ·
                refine ⟨6760167102314393752787285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4506778068209595835191523 6760167102314393752787285)
                ·
                  refine ⟨19805177057561700447619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 6760167102314393752787285 19805177057561700447619)
                  ·
                    rfl

theorem cell22_173567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 1, 10].length) (baseStart_173567 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_173567 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_173567 prefixEnd_173567 := by exact prefixLift 173567
  have htrace : WordTrace (prefixWord ++ tailWord_173567) baseStart_173567 baseEnd_173567 := by
    simpa [prefixWord, tailWord_173567, baseEnd_173567] using wordTrace_append hprefix tailTrace_173567
  have hstable : (prefixWord ++ tailWord_173567).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173567).length < 2 ^ (prefixWord ++ tailWord_173567).sum := by decide
  have hdescent : baseEnd_173567 < baseStart_173567 := by decide
  rcases family_descends (prefixWord ++ tailWord_173567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173588 : List Nat := [2, 4, 3, 1, 2, 1, 1, 1, 2, 5]
def baseStart_173588 : Nat := 118140960795 + 173588 * 2 ^ 59
def prefixEnd_173588 : Nat := 4983230072969 + 3 ^ 40 * 173588 * 2
def baseEnd_173588 : Nat := 59422719901848046567793

theorem tailTrace_173588 : CollatzResearch.WordTrace tailWord_173588 prefixEnd_173588 59422719901848046567793 := by
  unfold tailWord_173588
  simp only [CollatzResearch.WordTrace]
  refine ⟨3165637247563898657616709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4220849663418531543488945 3165637247563898657616709)
  ·
    refine ⟨593556983918230998303133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3165637247563898657616709 593556983918230998303133)
    ·
      refine ⟨222583868969336624363675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 593556983918230998303133 222583868969336624363675)
      ·
        refine ⟨333875803454004936545513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 222583868969336624363675 333875803454004936545513)
        ·
          refine ⟨250406852590503702409135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 333875803454004936545513 250406852590503702409135)
          ·
            refine ⟨375610278885755553613703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 250406852590503702409135 375610278885755553613703)
            ·
              refine ⟨563415418328633330420555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 375610278885755553613703 563415418328633330420555)
              ·
                refine ⟨845123127492949995630833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 563415418328633330420555 845123127492949995630833)
                ·
                  refine ⟨633842345619712496723125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 845123127492949995630833 633842345619712496723125)
                  ·
                    refine ⟨59422719901848046567793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 633842345619712496723125 59422719901848046567793)
                    ·
                      rfl

theorem cell22_173588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 1, 1, 2, 5].length) (baseStart_173588 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_173588 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_173588 prefixEnd_173588 := by exact prefixLift 173588
  have htrace : WordTrace (prefixWord ++ tailWord_173588) baseStart_173588 baseEnd_173588 := by
    simpa [prefixWord, tailWord_173588, baseEnd_173588] using wordTrace_append hprefix tailTrace_173588
  have hstable : (prefixWord ++ tailWord_173588).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173588).length < 2 ^ (prefixWord ++ tailWord_173588).sum := by decide
  have hdescent : baseEnd_173588 < baseStart_173588 := by decide
  rcases family_descends (prefixWord ++ tailWord_173588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173599 : List Nat := [1, 1, 2, 4, 1, 1, 3, 3, 1, 5]
def baseStart_173599 : Nat := 118140960795 + 173599 * 2 ^ 59
def prefixEnd_173599 : Nat := 4983230072969 + 3 ^ 40 * 173599 * 2
def baseEnd_173599 : Nat := 59426485426647684542759

theorem tailTrace_173599 : CollatzResearch.WordTrace tailWord_173599 prefixEnd_173599 59426485426647684542759 := by
  unfold tailWord_173599
  simp only [CollatzResearch.WordTrace]
  refine ⟨6331675698087946193883851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4221117132058630795922567 6331675698087946193883851)
  ·
    refine ⟨9497513547131919290825777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6331675698087946193883851 9497513547131919290825777)
    ·
      refine ⟨7123135160348939468119333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9497513547131919290825777 7123135160348939468119333)
      ·
        refine ⟨1335587842565426150272375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7123135160348939468119333 1335587842565426150272375)
        ·
          refine ⟨2003381763848139225408563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1335587842565426150272375 2003381763848139225408563)
          ·
            refine ⟨3005072645772208838112845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2003381763848139225408563 3005072645772208838112845)
            ·
              refine ⟨1126902242164578314292317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3005072645772208838112845 1126902242164578314292317)
              ·
                refine ⟨422588340811716867859619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1126902242164578314292317 422588340811716867859619)
                ·
                  refine ⟨633882511217575301789429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 422588340811716867859619 633882511217575301789429)
                  ·
                    refine ⟨59426485426647684542759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 633882511217575301789429 59426485426647684542759)
                    ·
                      rfl

theorem cell22_173599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 3, 1, 5].length) (baseStart_173599 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_173599 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_173599 prefixEnd_173599 := by exact prefixLift 173599
  have htrace : WordTrace (prefixWord ++ tailWord_173599) baseStart_173599 baseEnd_173599 := by
    simpa [prefixWord, tailWord_173599, baseEnd_173599] using wordTrace_append hprefix tailTrace_173599
  have hstable : (prefixWord ++ tailWord_173599).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173599).length < 2 ^ (prefixWord ++ tailWord_173599).sum := by decide
  have hdescent : baseEnd_173599 < baseStart_173599 := by decide
  rcases family_descends (prefixWord ++ tailWord_173599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173650 : List Nat := [3, 2, 2, 1, 2, 3, 3, 1, 2, 3]
def baseStart_173650 : Nat := 118140960795 + 173650 * 2 ^ 59
def prefixEnd_173650 : Nat := 4983230072969 + 3 ^ 40 * 173650 * 2
def baseEnd_173650 : Nat := 59443943768900551517603

theorem tailTrace_173650 : CollatzResearch.WordTrace tailWord_173650 prefixEnd_173650 59443943768900551517603 := by
  unfold tailWord_173650
  simp only [CollatzResearch.WordTrace]
  refine ⟨1583383955225795475997601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4222357213935454602660269 1583383955225795475997601)
  ·
    refine ⟨1187537966419346606998201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1583383955225795475997601 1187537966419346606998201)
    ·
      refine ⟨890653474814509955248651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1187537966419346606998201 890653474814509955248651)
      ·
        refine ⟨1335980212221764932872977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 890653474814509955248651 1335980212221764932872977)
        ·
          refine ⟨1001985159166323699654733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1335980212221764932872977 1001985159166323699654733)
          ·
            refine ⟨375744434687371387370525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1001985159166323699654733 375744434687371387370525)
            ·
              refine ⟨140904163007764270263947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 375744434687371387370525 140904163007764270263947)
              ·
                refine ⟨211356244511646405395921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 140904163007764270263947 211356244511646405395921)
                ·
                  refine ⟨158517183383734804046941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 211356244511646405395921 158517183383734804046941)
                  ·
                    refine ⟨59443943768900551517603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 158517183383734804046941 59443943768900551517603)
                    ·
                      rfl

theorem cell22_173650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 3, 1, 2, 3].length) (baseStart_173650 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_173650 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_173650 prefixEnd_173650 := by exact prefixLift 173650
  have htrace : WordTrace (prefixWord ++ tailWord_173650) baseStart_173650 baseEnd_173650 := by
    simpa [prefixWord, tailWord_173650, baseEnd_173650] using wordTrace_append hprefix tailTrace_173650
  have hstable : (prefixWord ++ tailWord_173650).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173650).length < 2 ^ (prefixWord ++ tailWord_173650).sum := by decide
  have hdescent : baseEnd_173650 < baseStart_173650 := by decide
  rcases family_descends (prefixWord ++ tailWord_173650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173721 : List Nat := [1, 2, 1, 2, 1, 2, 2, 6, 1, 4]
def baseStart_173721 : Nat := 118140960795 + 173721 * 2 ^ 59
def prefixEnd_173721 : Nat := 4983230072969 + 3 ^ 40 * 173721 * 2
def baseEnd_173721 : Nat := 59468248519880032992385

theorem tailTrace_173721 : CollatzResearch.WordTrace tailWord_173721 prefixEnd_173721 59468248519880032992385 := by
  unfold tailWord_173721
  simp only [CollatzResearch.WordTrace]
  refine ⟨6336125403645961029825017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4224083602430640686550011 6336125403645961029825017)
  ·
    refine ⟨4752094052734470772368763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6336125403645961029825017 4752094052734470772368763)
    ·
      refine ⟨7128141079101706158553145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4752094052734470772368763 7128141079101706158553145)
      ·
        refine ⟨5346105809326279618914859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7128141079101706158553145 5346105809326279618914859)
        ·
          refine ⟨8019158713989419428372289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5346105809326279618914859 8019158713989419428372289)
          ·
            refine ⟨6014369035492064571279217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8019158713989419428372289 6014369035492064571279217)
            ·
              refine ⟨4510776776619048428459413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6014369035492064571279217 4510776776619048428459413)
              ·
                refine ⟨211442661404017895084035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 4510776776619048428459413 211442661404017895084035)
                ·
                  refine ⟨317163992106026842626053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 211442661404017895084035 317163992106026842626053)
                  ·
                    refine ⟨59468248519880032992385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 317163992106026842626053 59468248519880032992385)
                    ·
                      rfl

theorem cell22_173721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 6, 1, 4].length) (baseStart_173721 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_173721 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_173721 prefixEnd_173721 := by exact prefixLift 173721
  have htrace : WordTrace (prefixWord ++ tailWord_173721) baseStart_173721 baseEnd_173721 := by
    simpa [prefixWord, tailWord_173721, baseEnd_173721] using wordTrace_append hprefix tailTrace_173721
  have hstable : (prefixWord ++ tailWord_173721).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173721).length < 2 ^ (prefixWord ++ tailWord_173721).sum := by decide
  have hdescent : baseEnd_173721 < baseStart_173721 := by decide
  rcases family_descends (prefixWord ++ tailWord_173721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173768 : List Nat := [2, 1, 3, 1, 2, 2, 1, 5, 2, 3]
def baseStart_173768 : Nat := 118140960795 + 173768 * 2 ^ 59
def prefixEnd_173768 : Nat := 4983230072969 + 3 ^ 40 * 173768 * 2
def baseEnd_173768 : Nat := 59484337580387577067241

theorem tailTrace_173768 : CollatzResearch.WordTrace tailWord_173768 prefixEnd_173768 59484337580387577067241 := by
  unfold tailWord_173768
  simp only [CollatzResearch.WordTrace]
  refine ⟨3168919817237844028392979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4225226422983792037857305 3168919817237844028392979)
  ·
    refine ⟨4753379725856766042589469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3168919817237844028392979 4753379725856766042589469)
    ·
      refine ⟨1782517397196287265971051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4753379725856766042589469 1782517397196287265971051)
      ·
        refine ⟨2673776095794430898956577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1782517397196287265971051 2673776095794430898956577)
        ·
          refine ⟨2005332071845823174217433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2673776095794430898956577 2005332071845823174217433)
          ·
            refine ⟨1503999053884367380663075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2005332071845823174217433 1503999053884367380663075)
            ·
              refine ⟨2255998580826551070994613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1503999053884367380663075 2255998580826551070994613)
              ·
                refine ⟨211499866952489162905745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2255998580826551070994613 211499866952489162905745)
                ·
                  refine ⟨158624900214366872179309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 211499866952489162905745 158624900214366872179309)
                  ·
                    refine ⟨59484337580387577067241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 158624900214366872179309 59484337580387577067241)
                    ·
                      rfl

theorem cell22_173768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 5, 2, 3].length) (baseStart_173768 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_173768 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_173768 prefixEnd_173768 := by exact prefixLift 173768
  have htrace : WordTrace (prefixWord ++ tailWord_173768) baseStart_173768 baseEnd_173768 := by
    simpa [prefixWord, tailWord_173768, baseEnd_173768] using wordTrace_append hprefix tailTrace_173768
  have hstable : (prefixWord ++ tailWord_173768).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173768).length < 2 ^ (prefixWord ++ tailWord_173768).sum := by decide
  have hdescent : baseEnd_173768 < baseStart_173768 := by decide
  rcases family_descends (prefixWord ++ tailWord_173768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173789 : List Nat := [1, 4, 3, 3, 1, 2, 2, 1, 1, 4]
def baseStart_173789 : Nat := 118140960795 + 173789 * 2 ^ 59
def prefixEnd_173789 : Nat := 4983230072969 + 3 ^ 40 * 173789 * 2
def baseEnd_173789 : Nat := 59491526309550522292177

theorem tailTrace_173789 : CollatzResearch.WordTrace tailWord_173789 prefixEnd_173789 59491526309550522292177 := by
  unfold tailWord_173789
  simp only [CollatzResearch.WordTrace]
  refine ⟨6338605567399608643300421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4225737044933072428866947 6338605567399608643300421)
  ·
    refine ⟨1188488543887426620618829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6338605567399608643300421 1188488543887426620618829)
    ·
      refine ⟨445683203957784982732061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1188488543887426620618829 445683203957784982732061)
      ·
        refine ⟨167131201484169368524523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 445683203957784982732061 167131201484169368524523)
        ·
          refine ⟨250696802226254052786785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167131201484169368524523 250696802226254052786785)
          ·
            refine ⟨188022601669690539590089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 250696802226254052786785 188022601669690539590089)
            ·
              refine ⟨141016951252267904692567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 188022601669690539590089 141016951252267904692567)
              ·
                refine ⟨211525426878401857038851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 141016951252267904692567 211525426878401857038851)
                ·
                  refine ⟨317288140317602785558277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 211525426878401857038851 317288140317602785558277)
                  ·
                    refine ⟨59491526309550522292177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 317288140317602785558277 59491526309550522292177)
                    ·
                      rfl

theorem cell22_173789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 2, 1, 1, 4].length) (baseStart_173789 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_173789 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_173789 prefixEnd_173789 := by exact prefixLift 173789
  have htrace : WordTrace (prefixWord ++ tailWord_173789) baseStart_173789 baseEnd_173789 := by
    simpa [prefixWord, tailWord_173789, baseEnd_173789] using wordTrace_append hprefix tailTrace_173789
  have hstable : (prefixWord ++ tailWord_173789).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173789).length < 2 ^ (prefixWord ++ tailWord_173789).sum := by decide
  have hdescent : baseEnd_173789 < baseStart_173789 := by decide
  rcases family_descends (prefixWord ++ tailWord_173789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173847 : List Nat := [1, 1, 3, 4, 2, 1, 3, 3, 1, 3]
def baseStart_173847 : Nat := 118140960795 + 173847 * 2 ^ 59
def prefixEnd_173847 : Nat := 4983230072969 + 3 ^ 40 * 173847 * 2
def baseEnd_173847 : Nat := 59511380894857704341999

theorem tailTrace_173847 : CollatzResearch.WordTrace tailWord_173847 prefixEnd_173847 59511380894857704341999 := by
  unfold tailWord_173847
  simp only [CollatzResearch.WordTrace]
  refine ⟨6340721001189484548911795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4227147334126323032607863 6340721001189484548911795)
  ·
    refine ⟨9511081501784226823367693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6340721001189484548911795 9511081501784226823367693)
    ·
      refine ⟨3566655563169085058762885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9511081501784226823367693 3566655563169085058762885)
      ·
        refine ⟨668747918094203448518041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3566655563169085058762885 668747918094203448518041)
        ·
          refine ⟨501560938570652586388531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 668747918094203448518041 501560938570652586388531)
          ·
            refine ⟨752341407855978879582797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 501560938570652586388531 752341407855978879582797)
            ·
              refine ⟨282128027945992079843549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 752341407855978879582797 282128027945992079843549)
              ·
                refine ⟨105798010479747029941331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 282128027945992079843549 105798010479747029941331)
                ·
                  refine ⟨158697015719620544911997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 105798010479747029941331 158697015719620544911997)
                  ·
                    refine ⟨59511380894857704341999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 158697015719620544911997 59511380894857704341999)
                    ·
                      rfl

theorem cell22_173847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 3, 3, 1, 3].length) (baseStart_173847 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_173847 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_173847 prefixEnd_173847 := by exact prefixLift 173847
  have htrace : WordTrace (prefixWord ++ tailWord_173847) baseStart_173847 baseEnd_173847 := by
    simpa [prefixWord, tailWord_173847, baseEnd_173847] using wordTrace_append hprefix tailTrace_173847
  have hstable : (prefixWord ++ tailWord_173847).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173847).length < 2 ^ (prefixWord ++ tailWord_173847).sum := by decide
  have hdescent : baseEnd_173847 < baseStart_173847 := by decide
  rcases family_descends (prefixWord ++ tailWord_173847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173864 : List Nat := [2, 1, 5, 1, 1, 3, 3, 2, 1, 3]
def baseStart_173864 : Nat := 118140960795 + 173864 * 2 ^ 59
def prefixEnd_173864 : Nat := 4983230072969 + 3 ^ 40 * 173864 * 2
def baseEnd_173864 : Nat := 59517200342275326666947

theorem tailTrace_173864 : CollatzResearch.WordTrace tailWord_173864 prefixEnd_173864 59517200342275326666947 := by
  unfold tailWord_173864
  simp only [CollatzResearch.WordTrace]
  refine ⟨3170670521063948226140323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4227560694751930968187097 3170670521063948226140323)
  ·
    refine ⟨4756005781595922339210485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3170670521063948226140323 4756005781595922339210485)
    ·
      refine ⟨445875542024617719300983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4756005781595922339210485 445875542024617719300983)
      ·
        refine ⟨668813313036926578951475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 445875542024617719300983 668813313036926578951475)
        ·
          refine ⟨1003219969555389868427213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 668813313036926578951475 1003219969555389868427213)
          ·
            refine ⟨376207488583271200660205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1003219969555389868427213 376207488583271200660205)
            ·
              refine ⟨141077808218726700247577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 376207488583271200660205 141077808218726700247577)
              ·
                refine ⟨105808356164045025185683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 141077808218726700247577 105808356164045025185683)
                ·
                  refine ⟨158712534246067537778525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 105808356164045025185683 158712534246067537778525)
                  ·
                    refine ⟨59517200342275326666947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 158712534246067537778525 59517200342275326666947)
                    ·
                      rfl

theorem cell22_173864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 3, 2, 1, 3].length) (baseStart_173864 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_173864 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_173864 prefixEnd_173864 := by exact prefixLift 173864
  have htrace : WordTrace (prefixWord ++ tailWord_173864) baseStart_173864 baseEnd_173864 := by
    simpa [prefixWord, tailWord_173864, baseEnd_173864] using wordTrace_append hprefix tailTrace_173864
  have hstable : (prefixWord ++ tailWord_173864).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173864).length < 2 ^ (prefixWord ++ tailWord_173864).sum := by decide
  have hdescent : baseEnd_173864 < baseStart_173864 := by decide
  rcases family_descends (prefixWord ++ tailWord_173864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173877 : List Nat := [1, 3, 3, 1, 4, 2, 2, 1, 5]
def baseStart_173877 : Nat := 118140960795 + 173877 * 2 ^ 59
def prefixEnd_173877 : Nat := 4983230072969 + 3 ^ 40 * 173877 * 2
def baseEnd_173877 : Nat := 19840550169315875363969

theorem tailTrace_173877 : CollatzResearch.WordTrace tailWord_173877 prefixEnd_173877 19840550169315875363969 := by
  unfold tailWord_173877
  simp only [CollatzResearch.WordTrace]
  refine ⟨6341815191080799672503885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4227876794053866448335923 6341815191080799672503885)
  ·
    refine ⟨2378180696655299877188957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6341815191080799672503885 2378180696655299877188957)
    ·
      refine ⟨891817761245737453945859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2378180696655299877188957 891817761245737453945859)
      ·
        refine ⟨1337726641868606180918789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 891817761245737453945859 1337726641868606180918789)
        ·
          refine ⟨250823745350363658922273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1337726641868606180918789 250823745350363658922273)
          ·
            refine ⟨188117809012772744191705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 250823745350363658922273 188117809012772744191705)
            ·
              refine ⟨141088356759579558143779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 188117809012772744191705 141088356759579558143779)
              ·
                refine ⟨211632535139369337215669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 141088356759579558143779 211632535139369337215669)
                ·
                  refine ⟨19840550169315875363969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 211632535139369337215669 19840550169315875363969)
                  ·
                    rfl

theorem cell22_173877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 2, 1, 5].length) (baseStart_173877 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_173877 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_173877 prefixEnd_173877 := by exact prefixLift 173877
  have htrace : WordTrace (prefixWord ++ tailWord_173877) baseStart_173877 baseEnd_173877 := by
    simpa [prefixWord, tailWord_173877, baseEnd_173877] using wordTrace_append hprefix tailTrace_173877
  have hstable : (prefixWord ++ tailWord_173877).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173877).length < 2 ^ (prefixWord ++ tailWord_173877).sum := by decide
  have hdescent : baseEnd_173877 < baseStart_173877 := by decide
  rcases family_descends (prefixWord ++ tailWord_173877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173920 : List Nat := [2, 1, 1, 3, 3, 2, 1, 4, 2, 3]
def baseStart_173920 : Nat := 118140960795 + 173920 * 2 ^ 59
def prefixEnd_173920 : Nat := 4983230072969 + 3 ^ 40 * 173920 * 2
def baseEnd_173920 : Nat := 59536370286709847266775

theorem tailTrace_173920 : CollatzResearch.WordTrace tailWord_173920 prefixEnd_173920 59536370286709847266775 := by
  unfold tailWord_173920
  simp only [CollatzResearch.WordTrace]
  refine ⟨3171691764962509008159607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4228922353283345344212809 3171691764962509008159607)
  ·
    refine ⟨4757537647443763512239411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3171691764962509008159607 4757537647443763512239411)
    ·
      refine ⟨7136306471165645268359117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4757537647443763512239411 7136306471165645268359117)
      ·
        refine ⟨2676114926687116975634669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7136306471165645268359117 2676114926687116975634669)
        ·
          refine ⟨1003543097507668865863001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2676114926687116975634669 1003543097507668865863001)
          ·
            refine ⟨752657323130751649397251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1003543097507668865863001 752657323130751649397251)
            ·
              refine ⟨1128985984696127474095877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 752657323130751649397251 1128985984696127474095877)
              ·
                refine ⟨211684872130523901392977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1128985984696127474095877 211684872130523901392977)
                ·
                  refine ⟨158763654097892926044733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 211684872130523901392977 158763654097892926044733)
                  ·
                    refine ⟨59536370286709847266775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 158763654097892926044733 59536370286709847266775)
                    ·
                      rfl

theorem cell22_173920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 4, 2, 3].length) (baseStart_173920 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_173920 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_173920 prefixEnd_173920 := by exact prefixLift 173920
  have htrace : WordTrace (prefixWord ++ tailWord_173920) baseStart_173920 baseEnd_173920 := by
    simpa [prefixWord, tailWord_173920, baseEnd_173920] using wordTrace_append hprefix tailTrace_173920
  have hstable : (prefixWord ++ tailWord_173920).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173920).length < 2 ^ (prefixWord ++ tailWord_173920).sum := by decide
  have hdescent : baseEnd_173920 < baseStart_173920 := by decide
  rcases family_descends (prefixWord ++ tailWord_173920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173922 : List Nat := [3, 3, 2, 1, 2, 2, 1, 4, 4]
def baseStart_173922 : Nat := 118140960795 + 173922 * 2 ^ 59
def prefixEnd_173922 : Nat := 4983230072969 + 3 ^ 40 * 173922 * 2
def baseEnd_173922 : Nat := 19845684975860836238923

theorem tailTrace_173922 : CollatzResearch.WordTrace tailWord_173922 prefixEnd_173922 19845684975860836238923 := by
  unfold tailWord_173922
  simp only [CollatzResearch.WordTrace]
  refine ⟨1585864118979443089473005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4228970983945181571928013 1585864118979443089473005)
  ·
    refine ⟨594699044617291158552377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1585864118979443089473005 594699044617291158552377)
    ·
      refine ⟨446024283462968368914283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 594699044617291158552377 446024283462968368914283)
      ·
        refine ⟨669036425194452553371425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 446024283462968368914283 669036425194452553371425)
        ·
          refine ⟨501777318895839415028569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 669036425194452553371425 501777318895839415028569)
          ·
            refine ⟨376332989171879561271427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 501777318895839415028569 376332989171879561271427)
            ·
              refine ⟨564499483757819341907141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 376332989171879561271427 564499483757819341907141)
              ·
                refine ⟨105843653204591126607589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 564499483757819341907141 105843653204591126607589)
                ·
                  refine ⟨19845684975860836238923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 105843653204591126607589 19845684975860836238923)
                  ·
                    rfl

theorem cell22_173922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 1, 4, 4].length) (baseStart_173922 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_173922 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_173922 prefixEnd_173922 := by exact prefixLift 173922
  have htrace : WordTrace (prefixWord ++ tailWord_173922) baseStart_173922 baseEnd_173922 := by
    simpa [prefixWord, tailWord_173922, baseEnd_173922] using wordTrace_append hprefix tailTrace_173922
  have hstable : (prefixWord ++ tailWord_173922).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173922).length < 2 ^ (prefixWord ++ tailWord_173922).sum := by decide
  have hdescent : baseEnd_173922 < baseStart_173922 := by decide
  rcases family_descends (prefixWord ++ tailWord_173922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173931 : List Nat := [1, 1, 1, 1, 2, 2, 3, 2, 2, 7]
def baseStart_173931 : Nat := 118140960795 + 173931 * 2 ^ 59
def prefixEnd_173931 : Nat := 4983230072969 + 3 ^ 40 * 173931 * 2
def baseEnd_173931 : Nat := 59540135811509485241741

theorem tailTrace_173931 : CollatzResearch.WordTrace tailWord_173931 prefixEnd_173931 59540135811509485241741 := by
  unfold tailWord_173931
  simp only [CollatzResearch.WordTrace]
  refine ⟨6343784732885166894969647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4229189821923444596646431 6343784732885166894969647)
  ·
    refine ⟨9515677099327750342454471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6343784732885166894969647 9515677099327750342454471)
    ·
      refine ⟨14273515648991625513681707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9515677099327750342454471 14273515648991625513681707)
      ·
        refine ⟨21410273473487438270522561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14273515648991625513681707 21410273473487438270522561)
        ·
          refine ⟨16057705105115578702891921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21410273473487438270522561 16057705105115578702891921)
          ·
            refine ⟨12043278828836684027168941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16057705105115578702891921 12043278828836684027168941)
            ·
              refine ⟨4516229560813756510188353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12043278828836684027168941 4516229560813756510188353)
              ·
                refine ⟨3387172170610317382641265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4516229560813756510188353 3387172170610317382641265)
                ·
                  refine ⟨2540379127957738036980949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3387172170610317382641265 2540379127957738036980949)
                  ·
                    refine ⟨59540135811509485241741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2540379127957738036980949 59540135811509485241741)
                    ·
                      rfl

theorem cell22_173931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 2, 2, 7].length) (baseStart_173931 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_173931 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_173931 prefixEnd_173931 := by exact prefixLift 173931
  have htrace : WordTrace (prefixWord ++ tailWord_173931) baseStart_173931 baseEnd_173931 := by
    simpa [prefixWord, tailWord_173931, baseEnd_173931] using wordTrace_append hprefix tailTrace_173931
  have hstable : (prefixWord ++ tailWord_173931).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173931).length < 2 ^ (prefixWord ++ tailWord_173931).sum := by decide
  have hdescent : baseEnd_173931 < baseStart_173931 := by decide
  rcases family_descends (prefixWord ++ tailWord_173931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173933 : List Nat := [1, 5, 1, 1, 1, 1, 5, 7]
def baseStart_173933 : Nat := 118140960795 + 173933 * 2 ^ 59
def prefixEnd_173933 : Nat := 4983230072969 + 3 ^ 40 * 173933 * 2
def baseEnd_173933 : Nat := 6615646716931349632415

theorem tailTrace_173933 : CollatzResearch.WordTrace tailWord_173933 prefixEnd_173933 6615646716931349632415 := by
  unfold tailWord_173933
  simp only [CollatzResearch.WordTrace]
  refine ⟨6343857678877921236542453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4229238452585280824361635 6343857678877921236542453)
  ·
    refine ⟨594736657394805115925855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6343857678877921236542453 594736657394805115925855)
    ·
      refine ⟨892104986092207673888783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 594736657394805115925855 892104986092207673888783)
      ·
        refine ⟨1338157479138311510833175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 892104986092207673888783 1338157479138311510833175)
        ·
          refine ⟨2007236218707467266249763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1338157479138311510833175 2007236218707467266249763)
          ·
            refine ⟨3010854328061200899374645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2007236218707467266249763 3010854328061200899374645)
            ·
              refine ⟨282267593255737584316373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3010854328061200899374645 282267593255737584316373)
              ·
                refine ⟨6615646716931349632415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 282267593255737584316373 6615646716931349632415)
                ·
                  rfl

theorem cell22_173933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 5, 7].length) (baseStart_173933 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_173933 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_173933 prefixEnd_173933 := by exact prefixLift 173933
  have htrace : WordTrace (prefixWord ++ tailWord_173933) baseStart_173933 baseEnd_173933 := by
    simpa [prefixWord, tailWord_173933, baseEnd_173933] using wordTrace_append hprefix tailTrace_173933
  have hstable : (prefixWord ++ tailWord_173933).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173933).length < 2 ^ (prefixWord ++ tailWord_173933).sum := by decide
  have hdescent : baseEnd_173933 < baseStart_173933 := by decide
  rcases family_descends (prefixWord ++ tailWord_173933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174117 : List Nat := [1, 3, 1, 2, 2, 4, 1, 2, 3, 3]
def baseStart_174117 : Nat := 118140960795 + 174117 * 2 ^ 59
def prefixEnd_174117 : Nat := 4983230072969 + 3 ^ 40 * 174117 * 2
def baseEnd_174117 : Nat := 59603807412667000091171

theorem tailTrace_174117 : CollatzResearch.WordTrace tailWord_174117 prefixEnd_174117 59603807412667000091171 := by
  unfold tailWord_174117
  simp only [CollatzResearch.WordTrace]
  refine ⟨6350568710211320661240605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4233712473474213774160403 6350568710211320661240605)
  ·
    refine ⟨2381463266329245247965227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6350568710211320661240605 2381463266329245247965227)
    ·
      refine ⟨3572194899493867871947841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2381463266329245247965227 3572194899493867871947841)
      ·
        refine ⟨2679146174620400903960881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3572194899493867871947841 2679146174620400903960881)
        ·
          refine ⟨2009359630965300677970661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2679146174620400903960881 2009359630965300677970661)
          ·
            refine ⟨376754930805993877119499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2009359630965300677970661 376754930805993877119499)
            ·
              refine ⟨565132396208990815679249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 376754930805993877119499 565132396208990815679249)
              ·
                refine ⟨423849297156743111759437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 565132396208990815679249 423849297156743111759437)
                ·
                  refine ⟨158943486433778666909789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 423849297156743111759437 158943486433778666909789)
                  ·
                    refine ⟨59603807412667000091171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 158943486433778666909789 59603807412667000091171)
                    ·
                      rfl

theorem cell22_174117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 1, 2, 3, 3].length) (baseStart_174117 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_174117 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_174117 prefixEnd_174117 := by exact prefixLift 174117
  have htrace : WordTrace (prefixWord ++ tailWord_174117) baseStart_174117 baseEnd_174117 := by
    simpa [prefixWord, tailWord_174117, baseEnd_174117] using wordTrace_append hprefix tailTrace_174117
  have hstable : (prefixWord ++ tailWord_174117).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174117).length < 2 ^ (prefixWord ++ tailWord_174117).sum := by decide
  have hdescent : baseEnd_174117 < baseStart_174117 := by decide
  rcases family_descends (prefixWord ++ tailWord_174117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174119 : List Nat := [1, 1, 7, 1, 2, 1, 3, 6]
def baseStart_174119 : Nat := 118140960795 + 174119 * 2 ^ 59
def prefixEnd_174119 : Nat := 4983230072969 + 3 ^ 40 * 174119 * 2
def baseEnd_174119 : Nat := 6622721339282184615685

theorem tailTrace_174119 : CollatzResearch.WordTrace tailWord_174119 prefixEnd_174119 6622721339282184615685 := by
  unfold tailWord_174119
  simp only [CollatzResearch.WordTrace]
  refine ⟨6350641656204075002813411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4233761104136050001875607 6350641656204075002813411)
  ·
    refine ⟨9525962484306112504220117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6350641656204075002813411 9525962484306112504220117)
    ·
      refine ⟨223264745725924511817659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 9525962484306112504220117 223264745725924511817659)
      ·
        refine ⟨334897118588886767726489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 223264745725924511817659 334897118588886767726489)
        ·
          refine ⟨251172838941665075794867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 334897118588886767726489 251172838941665075794867)
          ·
            refine ⟨376759258412497613692301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 251172838941665075794867 376759258412497613692301)
            ·
              refine ⟨141284721904686605134613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 376759258412497613692301 141284721904686605134613)
              ·
                refine ⟨6622721339282184615685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 141284721904686605134613 6622721339282184615685)
                ·
                  rfl

theorem cell22_174119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 3, 6].length) (baseStart_174119 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_174119 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_174119 prefixEnd_174119 := by exact prefixLift 174119
  have htrace : WordTrace (prefixWord ++ tailWord_174119) baseStart_174119 baseEnd_174119 := by
    simpa [prefixWord, tailWord_174119, baseEnd_174119] using wordTrace_append hprefix tailTrace_174119
  have hstable : (prefixWord ++ tailWord_174119).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174119).length < 2 ^ (prefixWord ++ tailWord_174119).sum := by decide
  have hdescent : baseEnd_174119 < baseStart_174119 := by decide
  rcases family_descends (prefixWord ++ tailWord_174119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174209 : List Nat := [1, 2, 4, 2, 3, 2, 1, 1, 6]
def baseStart_174209 : Nat := 118140960795 + 174209 * 2 ^ 59
def prefixEnd_174209 : Nat := 4983230072969 + 3 ^ 40 * 174209 * 2
def baseEnd_174209 : Nat := 19878433630936475596963

theorem tailTrace_174209 : CollatzResearch.WordTrace tailWord_174209 prefixEnd_174209 19878433630936475596963 := by
  unfold tailWord_174209
  simp only [CollatzResearch.WordTrace]
  refine ⟨6353924225878020373589681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4235949483918680249059787 6353924225878020373589681)
  ·
    refine ⟨4765443169408515280192261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6353924225878020373589681 4765443169408515280192261)
    ·
      refine ⟨893520594264096615036049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4765443169408515280192261 893520594264096615036049)
      ·
        refine ⟨670140445698072461277037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 893520594264096615036049 670140445698072461277037)
        ·
          refine ⟨251302667136777172978889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 670140445698072461277037 251302667136777172978889)
          ·
            refine ⟨188477000352582879734167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 251302667136777172978889 188477000352582879734167)
            ·
              refine ⟨282715500528874319601251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 188477000352582879734167 282715500528874319601251)
              ·
                refine ⟨424073250793311479401877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 282715500528874319601251 424073250793311479401877)
                ·
                  refine ⟨19878433630936475596963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 424073250793311479401877 19878433630936475596963)
                  ·
                    rfl

theorem cell22_174209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 1, 1, 6].length) (baseStart_174209 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_174209 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_174209 prefixEnd_174209 := by exact prefixLift 174209
  have htrace : WordTrace (prefixWord ++ tailWord_174209) baseStart_174209 baseEnd_174209 := by
    simpa [prefixWord, tailWord_174209, baseEnd_174209] using wordTrace_append hprefix tailTrace_174209
  have hstable : (prefixWord ++ tailWord_174209).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174209).length < 2 ^ (prefixWord ++ tailWord_174209).sum := by decide
  have hdescent : baseEnd_174209 < baseStart_174209 := by decide
  rcases family_descends (prefixWord ++ tailWord_174209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174228 : List Nat := [2, 4, 2, 3, 1, 2, 1, 2, 1, 4]
def baseStart_174228 : Nat := 118140960795 + 174228 * 2 ^ 59
def prefixEnd_174228 : Nat := 4983230072969 + 3 ^ 40 * 174228 * 2
def baseEnd_174228 : Nat := 59641804981099710565831

theorem tailTrace_174228 : CollatzResearch.WordTrace tailWord_174228 prefixEnd_174228 59641804981099710565831 := by
  unfold tailWord_174228
  simp only [CollatzResearch.WordTrace]
  refine ⟨3177308606404593309265669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4236411475206124412354225 3177308606404593309265669)
  ·
    refine ⟨595745363700861245487313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3177308606404593309265669 595745363700861245487313)
    ·
      refine ⟨446809022775645934115485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 595745363700861245487313 446809022775645934115485)
      ·
        refine ⟨167553383540867225293307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 446809022775645934115485 167553383540867225293307)
        ·
          refine ⟨251330075311300837939961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167553383540867225293307 251330075311300837939961)
          ·
            refine ⟨188497556483475628454971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 251330075311300837939961 188497556483475628454971)
            ·
              refine ⟨282746334725213442682457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 188497556483475628454971 282746334725213442682457)
              ·
                refine ⟨212059751043910082011843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 282746334725213442682457 212059751043910082011843)
                ·
                  refine ⟨318089626565865123017765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 212059751043910082011843 318089626565865123017765)
                  ·
                    refine ⟨59641804981099710565831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 318089626565865123017765 59641804981099710565831)
                    ·
                      rfl

theorem cell22_174228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 1, 2, 1, 4].length) (baseStart_174228 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_174228 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_174228 prefixEnd_174228 := by exact prefixLift 174228
  have htrace : WordTrace (prefixWord ++ tailWord_174228) baseStart_174228 baseEnd_174228 := by
    simpa [prefixWord, tailWord_174228, baseEnd_174228] using wordTrace_append hprefix tailTrace_174228
  have hstable : (prefixWord ++ tailWord_174228).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174228).length < 2 ^ (prefixWord ++ tailWord_174228).sum := by decide
  have hdescent : baseEnd_174228 < baseStart_174228 := by decide
  rcases family_descends (prefixWord ++ tailWord_174228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174239 : List Nat := [1, 1, 2, 6, 1, 2, 2, 1, 2, 4]
def baseStart_174239 : Nat := 118140960795 + 174239 * 2 ^ 59
def prefixEnd_174239 : Nat := 4983230072969 + 3 ^ 40 * 174239 * 2
def baseEnd_174239 : Nat := 59645570505899348540797

theorem tailTrace_174239 : CollatzResearch.WordTrace tailWord_174239 prefixEnd_174239 59645570505899348540797 := by
  unfold tailWord_174239
  simp only [CollatzResearch.WordTrace]
  refine ⟨6355018415769335497181771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4236678943846223664787847 6355018415769335497181771)
  ·
    refine ⟨9532527623654003245772657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6355018415769335497181771 9532527623654003245772657)
    ·
      refine ⟨7149395717740502434329493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9532527623654003245772657 7149395717740502434329493)
      ·
        refine ⟨335127924269086051609195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 7149395717740502434329493 335127924269086051609195)
        ·
          refine ⟨502691886403629077413793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 335127924269086051609195 502691886403629077413793)
          ·
            refine ⟨377018914802721808060345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 502691886403629077413793 377018914802721808060345)
            ·
              refine ⟨282764186102041356045259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 377018914802721808060345 282764186102041356045259)
              ·
                refine ⟨424146279153062034067889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 282764186102041356045259 424146279153062034067889)
                ·
                  refine ⟨318109709364796525550917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 424146279153062034067889 318109709364796525550917)
                  ·
                    refine ⟨59645570505899348540797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 318109709364796525550917 59645570505899348540797)
                    ·
                      rfl

theorem cell22_174239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 2, 1, 2, 4].length) (baseStart_174239 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_174239 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_174239 prefixEnd_174239 := by exact prefixLift 174239
  have htrace : WordTrace (prefixWord ++ tailWord_174239) baseStart_174239 baseEnd_174239 := by
    simpa [prefixWord, tailWord_174239, baseEnd_174239] using wordTrace_append hprefix tailTrace_174239
  have hstable : (prefixWord ++ tailWord_174239).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174239).length < 2 ^ (prefixWord ++ tailWord_174239).sum := by decide
  have hdescent : baseEnd_174239 < baseStart_174239 := by decide
  rcases family_descends (prefixWord ++ tailWord_174239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174254 : List Nat := [4, 1, 4, 2, 1, 10]
def baseStart_174254 : Nat := 118140960795 + 174254 * 2 ^ 59
def prefixEnd_174254 : Nat := 4983230072969 + 3 ^ 40 * 174254 * 2
def baseEnd_174254 : Nat := 736428460647460610071

theorem tailTrace_174254 : CollatzResearch.WordTrace tailWord_174254 prefixEnd_174254 736428460647460610071 := by
  unfold tailWord_174254
  simp only [CollatzResearch.WordTrace]
  refine ⟨794445688839374132372227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4237043673809995372651877 794445688839374132372227)
  ·
    refine ⟨1191668533259061198558341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 794445688839374132372227 1191668533259061198558341)
    ·
      refine ⟨223437849986073974729689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1191668533259061198558341 223437849986073974729689)
      ·
        refine ⟨167578387489555481047267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 223437849986073974729689 167578387489555481047267)
        ·
          refine ⟨251367581234333221570901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167578387489555481047267 251367581234333221570901)
          ·
            refine ⟨736428460647460610071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 251367581234333221570901 736428460647460610071)
            ·
              rfl

theorem cell22_174254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 10].length) (baseStart_174254 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_174254 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_174254 prefixEnd_174254 := by exact prefixLift 174254
  have htrace : WordTrace (prefixWord ++ tailWord_174254) baseStart_174254 baseEnd_174254 := by
    simpa [prefixWord, tailWord_174254, baseEnd_174254] using wordTrace_append hprefix tailTrace_174254
  have hstable : (prefixWord ++ tailWord_174254).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174254).length < 2 ^ (prefixWord ++ tailWord_174254).sum := by decide
  have hdescent : baseEnd_174254 < baseStart_174254 := by decide
  rcases family_descends (prefixWord ++ tailWord_174254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174260 : List Nat := [2, 5, 3, 1, 1, 1, 1, 4, 4]
def baseStart_174260 : Nat := 118140960795 + 174260 * 2 ^ 59
def prefixEnd_174260 : Nat := 4983230072969 + 3 ^ 40 * 174260 * 2
def baseEnd_174260 : Nat := 19884253078354097921911

theorem tailTrace_174260 : CollatzResearch.WordTrace tailWord_174260 prefixEnd_174260 19884253078354097921911 := by
  unfold tailWord_174260
  simp only [CollatzResearch.WordTrace]
  refine ⟨3177892174346628041848117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4237189565795504055797489 3177892174346628041848117)
  ·
    refine ⟨297927391344996378923261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3177892174346628041848117 297927391344996378923261)
    ·
      refine ⟨111722771754373642096223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 297927391344996378923261 111722771754373642096223)
      ·
        refine ⟨167584157631560463144335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111722771754373642096223 167584157631560463144335)
        ·
          refine ⟨251376236447340694716503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167584157631560463144335 251376236447340694716503)
          ·
            refine ⟨377064354671011042074755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 251376236447340694716503 377064354671011042074755)
            ·
              refine ⟨565596532006516563112133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 377064354671011042074755 565596532006516563112133)
              ·
                refine ⟨106049349751221855583525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 565596532006516563112133 106049349751221855583525)
                ·
                  refine ⟨19884253078354097921911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 106049349751221855583525 19884253078354097921911)
                  ·
                    rfl

theorem cell22_174260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 1, 4, 4].length) (baseStart_174260 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_174260 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_174260 prefixEnd_174260 := by exact prefixLift 174260
  have htrace : WordTrace (prefixWord ++ tailWord_174260) baseStart_174260 baseEnd_174260 := by
    simpa [prefixWord, tailWord_174260, baseEnd_174260] using wordTrace_append hprefix tailTrace_174260
  have hstable : (prefixWord ++ tailWord_174260).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174260).length < 2 ^ (prefixWord ++ tailWord_174260).sum := by decide
  have hdescent : baseEnd_174260 < baseStart_174260 := by decide
  rcases family_descends (prefixWord ++ tailWord_174260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174282 : List Nat := [3, 1, 2, 1, 3, 1, 1, 5, 5]
def baseStart_174282 : Nat := 118140960795 + 174282 * 2 ^ 59
def prefixEnd_174282 : Nat := 4983230072969 + 3 ^ 40 * 174282 * 2
def baseEnd_174282 : Nat := 19886763428220523238555

theorem tailTrace_174282 : CollatzResearch.WordTrace tailWord_174282 prefixEnd_174282 19886763428220523238555 := by
  unfold tailWord_174282
  simp only [CollatzResearch.WordTrace]
  refine ⟨1589146688653388460249275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4237724503075702560664733 1589146688653388460249275)
  ·
    refine ⟨2383720032980082690373913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1589146688653388460249275 2383720032980082690373913)
    ·
      refine ⟨1787790024735062017780435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2383720032980082690373913 1787790024735062017780435)
      ·
        refine ⟨2681685037102593026670653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1787790024735062017780435 2681685037102593026670653)
        ·
          refine ⟨1005631888913472385001495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2681685037102593026670653 1005631888913472385001495)
          ·
            refine ⟨1508447833370208577502243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1005631888913472385001495 1508447833370208577502243)
            ·
              refine ⟨2262671750055312866253365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1508447833370208577502243 2262671750055312866253365)
              ·
                refine ⟨212125476567685581211253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2262671750055312866253365 212125476567685581211253)
                ·
                  refine ⟨19886763428220523238555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 212125476567685581211253 19886763428220523238555)
                  ·
                    rfl

theorem cell22_174282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 5, 5].length) (baseStart_174282 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_174282 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_174282 prefixEnd_174282 := by exact prefixLift 174282
  have htrace : WordTrace (prefixWord ++ tailWord_174282) baseStart_174282 baseEnd_174282 := by
    simpa [prefixWord, tailWord_174282, baseEnd_174282] using wordTrace_append hprefix tailTrace_174282
  have hstable : (prefixWord ++ tailWord_174282).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174282).length < 2 ^ (prefixWord ++ tailWord_174282).sum := by decide
  have hdescent : baseEnd_174282 < baseStart_174282 := by decide
  rcases family_descends (prefixWord ++ tailWord_174282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174357 : List Nat := [1, 3, 2, 1, 2, 1, 4, 1, 1, 6]
def baseStart_174357 : Nat := 118140960795 + 174357 * 2 ^ 59
def prefixEnd_174357 : Nat := 4983230072969 + 3 ^ 40 * 174357 * 2
def baseEnd_174357 : Nat := 59685964317386374090435

theorem tailTrace_174357 : CollatzResearch.WordTrace tailWord_174357 prefixEnd_174357 59685964317386374090435 := by
  unfold tailWord_174357
  simp only [CollatzResearch.WordTrace]
  refine ⟨6359322229341841649977325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4239548152894561099984883 6359322229341841649977325)
  ·
    refine ⟨2384745836003190618741497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6359322229341841649977325 2384745836003190618741497)
    ·
      refine ⟨1788559377002392964056123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2384745836003190618741497 1788559377002392964056123)
      ·
        refine ⟨2682839065503589446084185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1788559377002392964056123 2682839065503589446084185)
        ·
          refine ⟨2012129299127692084563139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2682839065503589446084185 2012129299127692084563139)
          ·
            refine ⟨3018193948691538126844709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2012129299127692084563139 3018193948691538126844709)
            ·
              refine ⟨565911365379663398783383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3018193948691538126844709 565911365379663398783383)
              ·
                refine ⟨848867048069495098175075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 565911365379663398783383 848867048069495098175075)
                ·
                  refine ⟨1273300572104242647262613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 848867048069495098175075 1273300572104242647262613)
                  ·
                    refine ⟨59685964317386374090435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1273300572104242647262613 59685964317386374090435)
                    ·
                      rfl

theorem cell22_174357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 4, 1, 1, 6].length) (baseStart_174357 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_174357 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_174357 prefixEnd_174357 := by exact prefixLift 174357
  have htrace : WordTrace (prefixWord ++ tailWord_174357) baseStart_174357 baseEnd_174357 := by
    simpa [prefixWord, tailWord_174357, baseEnd_174357] using wordTrace_append hprefix tailTrace_174357
  have hstable : (prefixWord ++ tailWord_174357).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174357).length < 2 ^ (prefixWord ++ tailWord_174357).sum := by decide
  have hdescent : baseEnd_174357 < baseStart_174357 := by decide
  rcases family_descends (prefixWord ++ tailWord_174357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174359 : List Nat := [1, 1, 3, 4, 1, 2, 1, 2, 4, 3]
def baseStart_174359 : Nat := 118140960795 + 174359 * 2 ^ 59
def prefixEnd_174359 : Nat := 4983230072969 + 3 ^ 40 * 174359 * 2
def baseEnd_174359 : Nat := 59686648958259035540429

theorem tailTrace_174359 : CollatzResearch.WordTrace tailWord_174359 prefixEnd_174359 59686648958259035540429 := by
  unfold tailWord_174359
  simp only [CollatzResearch.WordTrace]
  refine ⟨6359395175334595991550131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4239596783556397327700087 6359395175334595991550131)
  ·
    refine ⟨9539092763001893987325197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6359395175334595991550131 9539092763001893987325197)
    ·
      refine ⟨3577159786125710245246949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9539092763001893987325197 3577159786125710245246949)
      ·
        refine ⟨670717459898570670983803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3577159786125710245246949 670717459898570670983803)
        ·
          refine ⟨1006076189847856006475705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 670717459898570670983803 1006076189847856006475705)
          ·
            refine ⟨754557142385892004856779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1006076189847856006475705 754557142385892004856779)
            ·
              refine ⟨1131835713578838007285169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 754557142385892004856779 1131835713578838007285169)
              ·
                refine ⟨848876785184128505463877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1131835713578838007285169 848876785184128505463877)
                ·
                  refine ⟨159164397222024094774477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 848876785184128505463877 159164397222024094774477)
                  ·
                    refine ⟨59686648958259035540429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 159164397222024094774477 59686648958259035540429)
                    ·
                      rfl

theorem cell22_174359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 2, 4, 3].length) (baseStart_174359 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_174359 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_174359 prefixEnd_174359 := by exact prefixLift 174359
  have htrace : WordTrace (prefixWord ++ tailWord_174359) baseStart_174359 baseEnd_174359 := by
    simpa [prefixWord, tailWord_174359, baseEnd_174359] using wordTrace_append hprefix tailTrace_174359
  have hstable : (prefixWord ++ tailWord_174359).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174359).length < 2 ^ (prefixWord ++ tailWord_174359).sum := by decide
  have hdescent : baseEnd_174359 < baseStart_174359 := by decide
  rcases family_descends (prefixWord ++ tailWord_174359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174372 : List Nat := [2, 3, 1, 3, 1, 2, 10]
def baseStart_174372 : Nat := 118140960795 + 174372 * 2 ^ 59
def prefixEnd_174372 : Nat := 4983230072969 + 3 ^ 40 * 174372 * 2
def baseEnd_174372 : Nat := 2210781449034493887607

theorem tailTrace_174372 : CollatzResearch.WordTrace tailWord_174372 prefixEnd_174372 2210781449034493887607 := by
  unfold tailWord_174372
  simp only [CollatzResearch.WordTrace]
  refine ⟨3179934662143749605886685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4239912882858332807848913 3179934662143749605886685)
  ·
    refine ⟨1192475498303906102207507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3179934662143749605886685 1192475498303906102207507)
    ·
      refine ⟨1788713247455859153311261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1192475498303906102207507 1788713247455859153311261)
      ·
        refine ⟨670767467795947182491723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1788713247455859153311261 670767467795947182491723)
        ·
          refine ⟨1006151201693920773737585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 670767467795947182491723 1006151201693920773737585)
          ·
            refine ⟨754613401270440580303189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1006151201693920773737585 754613401270440580303189)
            ·
              refine ⟨2210781449034493887607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 754613401270440580303189 2210781449034493887607)
              ·
                rfl

theorem cell22_174372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 10].length) (baseStart_174372 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_174372 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_174372 prefixEnd_174372 := by exact prefixLift 174372
  have htrace : WordTrace (prefixWord ++ tailWord_174372) baseStart_174372 baseEnd_174372 := by
    simpa [prefixWord, tailWord_174372, baseEnd_174372] using wordTrace_append hprefix tailTrace_174372
  have hstable : (prefixWord ++ tailWord_174372).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174372).length < 2 ^ (prefixWord ++ tailWord_174372).sum := by decide
  have hdescent : baseEnd_174372 < baseStart_174372 := by decide
  rcases family_descends (prefixWord ++ tailWord_174372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174378 : List Nat := [3, 1, 4, 2, 3, 1, 1, 1, 6]
def baseStart_174378 : Nat := 118140960795 + 174378 * 2 ^ 59
def prefixEnd_174378 : Nat := 4983230072969 + 3 ^ 40 * 174378 * 2
def baseEnd_174378 : Nat := 19897717682183106438457

theorem tailTrace_174378 : CollatzResearch.WordTrace tailWord_174378 prefixEnd_174378 19897717682183106438457 := by
  unfold tailWord_174378
  simp only [CollatzResearch.WordTrace]
  refine ⟨1590022040566440559122947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4240058774843841490994525 1590022040566440559122947)
  ·
    refine ⟨2385033060849660838684421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1590022040566440559122947 2385033060849660838684421)
    ·
      refine ⟨447193698909311407253329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2385033060849660838684421 447193698909311407253329)
      ·
        refine ⟨335395274181983555439997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 447193698909311407253329 335395274181983555439997)
        ·
          refine ⟨125773227818243833289999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 335395274181983555439997 125773227818243833289999)
          ·
            refine ⟨188659841727365749934999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125773227818243833289999 188659841727365749934999)
            ·
              refine ⟨282989762591048624902499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 188659841727365749934999 282989762591048624902499)
              ·
                refine ⟨424484643886572937353749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 282989762591048624902499 424484643886572937353749)
                ·
                  refine ⟨19897717682183106438457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 424484643886572937353749 19897717682183106438457)
                  ·
                    rfl

theorem cell22_174378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 1, 1, 6].length) (baseStart_174378 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_174378 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_174378 prefixEnd_174378 := by exact prefixLift 174378
  have htrace : WordTrace (prefixWord ++ tailWord_174378) baseStart_174378 baseEnd_174378 := by
    simpa [prefixWord, tailWord_174378, baseEnd_174378] using wordTrace_append hprefix tailTrace_174378
  have hstable : (prefixWord ++ tailWord_174378).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174378).length < 2 ^ (prefixWord ++ tailWord_174378).sum := by decide
  have hdescent : baseEnd_174378 < baseStart_174378 := by decide
  rcases family_descends (prefixWord ++ tailWord_174378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174393 : List Nat := [1, 2, 1, 6, 1, 1, 4, 1, 2, 3]
def baseStart_174393 : Nat := 118140960795 + 174393 * 2 ^ 59
def prefixEnd_174393 : Nat := 4983230072969 + 3 ^ 40 * 174393 * 2
def baseEnd_174393 : Nat := 59698287853094280190325

theorem tailTrace_174393 : CollatzResearch.WordTrace tailWord_174393 prefixEnd_174393 59698287853094280190325 := by
  unfold tailWord_174393
  simp only [CollatzResearch.WordTrace]
  refine ⟨6360635257211419798287833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4240423504807613198858555 6360635257211419798287833)
  ·
    refine ⟨4770476442908564848715875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6360635257211419798287833 4770476442908564848715875)
    ·
      refine ⟨7155714664362847273073813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4770476442908564848715875 7155714664362847273073813)
      ·
        refine ⟨335424124892008465925335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 7155714664362847273073813 335424124892008465925335)
        ·
          refine ⟨503136187338012698888003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 335424124892008465925335 503136187338012698888003)
          ·
            refine ⟨754704281007019048332005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 503136187338012698888003 754704281007019048332005)
            ·
              refine ⟨141507052688816071562251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 754704281007019048332005 141507052688816071562251)
              ·
                refine ⟨212260579033224107343377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 141507052688816071562251 212260579033224107343377)
                ·
                  refine ⟨159195434274918080507533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 212260579033224107343377 159195434274918080507533)
                  ·
                    refine ⟨59698287853094280190325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 159195434274918080507533 59698287853094280190325)
                    ·
                      rfl

theorem cell22_174393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 4, 1, 2, 3].length) (baseStart_174393 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_174393 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_174393 prefixEnd_174393 := by exact prefixLift 174393
  have htrace : WordTrace (prefixWord ++ tailWord_174393) baseStart_174393 baseEnd_174393 := by
    simpa [prefixWord, tailWord_174393, baseEnd_174393] using wordTrace_append hprefix tailTrace_174393
  have hstable : (prefixWord ++ tailWord_174393).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174393).length < 2 ^ (prefixWord ++ tailWord_174393).sum := by decide
  have hdescent : baseEnd_174393 < baseStart_174393 := by decide
  rcases family_descends (prefixWord ++ tailWord_174393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174496 : List Nat := [2, 1, 1, 4, 1, 3, 2, 4, 4]
def baseStart_174496 : Nat := 118140960795 + 174496 * 2 ^ 59
def prefixEnd_174496 : Nat := 4983230072969 + 3 ^ 40 * 174496 * 2
def baseEnd_174496 : Nat := 19911182286012114955003

theorem tailTrace_174496 : CollatzResearch.WordTrace tailWord_174496 prefixEnd_174496 19911182286012114955003 := by
  unfold tailWord_174496
  simp only [CollatzResearch.WordTrace]
  refine ⟨3182195987919134194643671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4242927983892178926191561 3182195987919134194643671)
  ·
    refine ⟨4773293981878701291965507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3182195987919134194643671 4773293981878701291965507)
    ·
      refine ⟨7159940972818051937948261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4773293981878701291965507 7159940972818051937948261)
      ·
        refine ⟨1342488932403384738365299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7159940972818051937948261 1342488932403384738365299)
        ·
          refine ⟨2013733398605077107547949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1342488932403384738365299 2013733398605077107547949)
          ·
            refine ⟨755150024476903915330481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2013733398605077107547949 755150024476903915330481)
            ·
              refine ⟨566362518357677936497861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 755150024476903915330481 566362518357677936497861)
              ·
                refine ⟨106192972192064613093349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 566362518357677936497861 106192972192064613093349)
                ·
                  refine ⟨19911182286012114955003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 106192972192064613093349 19911182286012114955003)
                  ·
                    rfl

theorem cell22_174496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 2, 4, 4].length) (baseStart_174496 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_174496 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_174496 prefixEnd_174496 := by exact prefixLift 174496
  have htrace : WordTrace (prefixWord ++ tailWord_174496) baseStart_174496 baseEnd_174496 := by
    simpa [prefixWord, tailWord_174496, baseEnd_174496] using wordTrace_append hprefix tailTrace_174496
  have hstable : (prefixWord ++ tailWord_174496).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174496).length < 2 ^ (prefixWord ++ tailWord_174496).sum := by decide
  have hdescent : baseEnd_174496 < baseStart_174496 := by decide
  rcases family_descends (prefixWord ++ tailWord_174496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174554 : List Nat := [3, 1, 1, 2, 3, 1, 2, 1, 2, 6]
def baseStart_174554 : Nat := 118140960795 + 174554 * 2 ^ 59
def prefixEnd_174554 : Nat := 4983230072969 + 3 ^ 40 * 174554 * 2
def baseEnd_174554 : Nat := 59753401443343526914831

theorem tailTrace_174554 : CollatzResearch.WordTrace tailWord_174554 prefixEnd_174554 59753401443343526914831 := by
  unfold tailWord_174554
  simp only [CollatzResearch.WordTrace]
  refine ⟨1591626852407036073724679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4244338273085429529932477 1591626852407036073724679)
  ·
    refine ⟨2387440278610554110587019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1591626852407036073724679 2387440278610554110587019)
    ·
      refine ⟨3581160417915831165880529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2387440278610554110587019 3581160417915831165880529)
      ·
        refine ⟨2685870313436873374410397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3581160417915831165880529 2685870313436873374410397)
        ·
          refine ⟨1007201367538827515403899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2685870313436873374410397 1007201367538827515403899)
          ·
            refine ⟨1510802051308241273105849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1007201367538827515403899 1510802051308241273105849)
            ·
              refine ⟨1133101538481180954829387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1510802051308241273105849 1133101538481180954829387)
              ·
                refine ⟨1699652307721771432244081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1133101538481180954829387 1699652307721771432244081)
                ·
                  refine ⟨1274739230791328574183061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1699652307721771432244081 1274739230791328574183061)
                  ·
                    refine ⟨59753401443343526914831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1274739230791328574183061 59753401443343526914831)
                    ·
                      rfl

theorem cell22_174554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 1, 2, 6].length) (baseStart_174554 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_174554 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_174554 prefixEnd_174554 := by exact prefixLift 174554
  have htrace : WordTrace (prefixWord ++ tailWord_174554) baseStart_174554 baseEnd_174554 := by
    simpa [prefixWord, tailWord_174554, baseEnd_174554] using wordTrace_append hprefix tailTrace_174554
  have hstable : (prefixWord ++ tailWord_174554).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174554).length < 2 ^ (prefixWord ++ tailWord_174554).sum := by decide
  have hdescent : baseEnd_174554 < baseStart_174554 := by decide
  rcases family_descends (prefixWord ++ tailWord_174554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174562 : List Nat := [3, 3, 3, 2, 1, 1, 1, 3, 2, 3]
def baseStart_174562 : Nat := 118140960795 + 174562 * 2 ^ 59
def prefixEnd_174562 : Nat := 4983230072969 + 3 ^ 40 * 174562 * 2
def baseEnd_174562 : Nat := 59756140006834172714807

theorem tailTrace_174562 : CollatzResearch.WordTrace tailWord_174562 prefixEnd_174562 59756140006834172714807 := by
  unfold tailWord_174562
  simp only [CollatzResearch.WordTrace]
  refine ⟨1591699798399790415297485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4244532795732774440793293 1591699798399790415297485)
  ·
    refine ⟨596887424399921405736557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1591699798399790415297485 596887424399921405736557)
    ·
      refine ⟨223832784149970527151209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 596887424399921405736557 223832784149970527151209)
      ·
        refine ⟨167874588112477895363407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 223832784149970527151209 167874588112477895363407)
        ·
          refine ⟨251811882168716843045111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167874588112477895363407 251811882168716843045111)
          ·
            refine ⟨377717823253075264567667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 251811882168716843045111 377717823253075264567667)
            ·
              refine ⟨566576734879612896851501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 377717823253075264567667 566576734879612896851501)
              ·
                refine ⟨212466275579854836319313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 566576734879612896851501 212466275579854836319313)
                ·
                  refine ⟨159349706684891127239485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 212466275579854836319313 159349706684891127239485)
                  ·
                    refine ⟨59756140006834172714807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 159349706684891127239485 59756140006834172714807)
                    ·
                      rfl

theorem cell22_174562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 1, 3, 2, 3].length) (baseStart_174562 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_174562 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_174562 prefixEnd_174562 := by exact prefixLift 174562
  have htrace : WordTrace (prefixWord ++ tailWord_174562) baseStart_174562 baseEnd_174562 := by
    simpa [prefixWord, tailWord_174562, baseEnd_174562] using wordTrace_append hprefix tailTrace_174562
  have hstable : (prefixWord ++ tailWord_174562).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174562).length < 2 ^ (prefixWord ++ tailWord_174562).sum := by decide
  have hdescent : baseEnd_174562 < baseStart_174562 := by decide
  rcases family_descends (prefixWord ++ tailWord_174562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174616 : List Nat := [2, 1, 2, 3, 3, 1, 1, 2, 3, 4]
def baseStart_174616 : Nat := 118140960795 + 174616 * 2 ^ 59
def prefixEnd_174616 : Nat := 4983230072969 + 3 ^ 40 * 174616 * 2
def baseEnd_174616 : Nat := 59774625310396031864641

theorem tailTrace_174616 : CollatzResearch.WordTrace tailWord_174616 prefixEnd_174616 59774625310396031864641 := by
  unfold tailWord_174616
  simp only [CollatzResearch.WordTrace]
  refine ⟨3184384367701764441827851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4245845823602352589103801 3184384367701764441827851)
  ·
    refine ⟨4776576551552646662741777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3184384367701764441827851 4776576551552646662741777)
    ·
      refine ⟨3582432413664484997056333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4776576551552646662741777 3582432413664484997056333)
      ·
        refine ⟨1343412155124181873896125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3582432413664484997056333 1343412155124181873896125)
        ·
          refine ⟨503779558171568202711047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1343412155124181873896125 503779558171568202711047)
          ·
            refine ⟨755669337257352304066571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 503779558171568202711047 755669337257352304066571)
            ·
              refine ⟨1133504005886028456099857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 755669337257352304066571 1133504005886028456099857)
              ·
                refine ⟨850128004414521342074893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1133504005886028456099857 850128004414521342074893)
                ·
                  refine ⟨318798001655445503278085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 850128004414521342074893 318798001655445503278085)
                  ·
                    refine ⟨59774625310396031864641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 318798001655445503278085 59774625310396031864641)
                    ·
                      rfl

theorem cell22_174616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 2, 3, 4].length) (baseStart_174616 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_174616 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_174616 prefixEnd_174616 := by exact prefixLift 174616
  have htrace : WordTrace (prefixWord ++ tailWord_174616) baseStart_174616 baseEnd_174616 := by
    simpa [prefixWord, tailWord_174616, baseEnd_174616] using wordTrace_append hprefix tailTrace_174616
  have hstable : (prefixWord ++ tailWord_174616).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174616).length < 2 ^ (prefixWord ++ tailWord_174616).sum := by decide
  have hdescent : baseEnd_174616 < baseStart_174616 := by decide
  rcases family_descends (prefixWord ++ tailWord_174616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174648 : List Nat := [2, 1, 2, 1, 4, 1, 4, 3, 4]
def baseStart_174648 : Nat := 118140960795 + 174648 * 2 ^ 59
def prefixEnd_174648 : Nat := 4983230072969 + 3 ^ 40 * 174648 * 2
def baseEnd_174648 : Nat := 19928526521452871688181

theorem tailTrace_174648 : CollatzResearch.WordTrace tailWord_174648 prefixEnd_174648 19928526521452871688181 := by
  unfold tailWord_174648
  simp only [CollatzResearch.WordTrace]
  refine ⟨3184967935643799174410299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4246623914191732232547065 3184967935643799174410299)
  ·
    refine ⟨4777451903465698761615449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3184967935643799174410299 4777451903465698761615449)
    ·
      refine ⟨3583088927599274071211587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4777451903465698761615449 3583088927599274071211587)
      ·
        refine ⟨5374633391398911106817381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3583088927599274071211587 5374633391398911106817381)
        ·
          refine ⟨1007743760887295832528259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5374633391398911106817381 1007743760887295832528259)
          ·
            refine ⟨1511615641330943748792389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1007743760887295832528259 1511615641330943748792389)
            ·
              refine ⟨283427932749551952898573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1511615641330943748792389 283427932749551952898573)
              ·
                refine ⟨106285474781081982336965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 283427932749551952898573 106285474781081982336965)
                ·
                  refine ⟨19928526521452871688181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 106285474781081982336965 19928526521452871688181)
                  ·
                    rfl

theorem cell22_174648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 4, 3, 4].length) (baseStart_174648 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_174648 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_174648 prefixEnd_174648 := by exact prefixLift 174648
  have htrace : WordTrace (prefixWord ++ tailWord_174648) baseStart_174648 baseEnd_174648 := by
    simpa [prefixWord, tailWord_174648, baseEnd_174648] using wordTrace_append hprefix tailTrace_174648
  have hstable : (prefixWord ++ tailWord_174648).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174648).length < 2 ^ (prefixWord ++ tailWord_174648).sum := by decide
  have hdescent : baseEnd_174648 < baseStart_174648 := by decide
  rcases family_descends (prefixWord ++ tailWord_174648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174650 : List Nat := [3, 1, 1, 1, 3, 5, 2, 1, 1, 4]
def baseStart_174650 : Nat := 118140960795 + 174650 * 2 ^ 59
def prefixEnd_174650 : Nat := 4983230072969 + 3 ^ 40 * 174650 * 2
def baseEnd_174650 : Nat := 59786264205231276514537

theorem tailTrace_174650 : CollatzResearch.WordTrace tailWord_174650 prefixEnd_174650 59786264205231276514537 := by
  unfold tailWord_174650
  simp only [CollatzResearch.WordTrace]
  refine ⟨1592502204320088172598351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4246672544853568460262269 1592502204320088172598351)
  ·
    refine ⟨2388753306480132258897527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1592502204320088172598351 2388753306480132258897527)
    ·
      refine ⟨3583129959720198388346291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2388753306480132258897527 3583129959720198388346291)
      ·
        refine ⟨5374694939580297582519437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3583129959720198388346291 5374694939580297582519437)
        ·
          refine ⟨2015510602342611593444789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5374694939580297582519437 2015510602342611593444789)
          ·
            refine ⟨188954118969619836885449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2015510602342611593444789 188954118969619836885449)
            ·
              refine ⟨141715589227214877664087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 188954118969619836885449 141715589227214877664087)
              ·
                refine ⟨212573383840822316496131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 141715589227214877664087 212573383840822316496131)
                ·
                  refine ⟨318860075761233474744197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 212573383840822316496131 318860075761233474744197)
                  ·
                    refine ⟨59786264205231276514537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 318860075761233474744197 59786264205231276514537)
                    ·
                      rfl

theorem cell22_174650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 2, 1, 1, 4].length) (baseStart_174650 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_174650 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_174650 prefixEnd_174650 := by exact prefixLift 174650
  have htrace : WordTrace (prefixWord ++ tailWord_174650) baseStart_174650 baseEnd_174650 := by
    simpa [prefixWord, tailWord_174650, baseEnd_174650] using wordTrace_append hprefix tailTrace_174650
  have hstable : (prefixWord ++ tailWord_174650).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174650).length < 2 ^ (prefixWord ++ tailWord_174650).sum := by decide
  have hdescent : baseEnd_174650 < baseStart_174650 := by decide
  rcases family_descends (prefixWord ++ tailWord_174650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174663 : List Nat := [1, 1, 4, 1, 4, 2, 1, 1, 4, 3]
def baseStart_174663 : Nat := 118140960795 + 174663 * 2 ^ 59
def prefixEnd_174663 : Nat := 4983230072969 + 3 ^ 40 * 174663 * 2
def baseEnd_174663 : Nat := 59790714370903575939497

theorem tailTrace_174663 : CollatzResearch.WordTrace tailWord_174663 prefixEnd_174663 59790714370903575939497 := by
  unfold tailWord_174663
  simp only [CollatzResearch.WordTrace]
  refine ⟨6370482966233255910616643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4246988644155503940411095 6370482966233255910616643)
  ·
    refine ⟨9555724449349883865924965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6370482966233255910616643 9555724449349883865924965)
    ·
      refine ⟨1791698334253103224860931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9555724449349883865924965 1791698334253103224860931)
      ·
        refine ⟨2687547501379654837291397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1791698334253103224860931 2687547501379654837291397)
        ·
          refine ⟨503915156508685281992137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2687547501379654837291397 503915156508685281992137)
          ·
            refine ⟨377936367381513961494103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 503915156508685281992137 377936367381513961494103)
            ·
              refine ⟨566904551072270942241155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 377936367381513961494103 566904551072270942241155)
              ·
                refine ⟨850356826608406413361733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 566904551072270942241155 850356826608406413361733)
                ·
                  refine ⟨159441904989076202505325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 850356826608406413361733 159441904989076202505325)
                  ·
                    refine ⟨59790714370903575939497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 159441904989076202505325 59790714370903575939497)
                    ·
                      rfl

theorem cell22_174663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 1, 1, 4, 3].length) (baseStart_174663 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_174663 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_174663 prefixEnd_174663 := by exact prefixLift 174663
  have htrace : WordTrace (prefixWord ++ tailWord_174663) baseStart_174663 baseEnd_174663 := by
    simpa [prefixWord, tailWord_174663, baseEnd_174663] using wordTrace_append hprefix tailTrace_174663
  have hstable : (prefixWord ++ tailWord_174663).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174663).length < 2 ^ (prefixWord ++ tailWord_174663).sum := by decide
  have hdescent : baseEnd_174663 < baseStart_174663 := by decide
  rcases family_descends (prefixWord ++ tailWord_174663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174710 : List Nat := [5, 1, 1, 2, 4, 1, 8]
def baseStart_174710 : Nat := 118140960795 + 174710 * 2 ^ 59
def prefixEnd_174710 : Nat := 4983230072969 + 3 ^ 40 * 174710 * 2
def baseEnd_174710 : Nat := 2215066793755967407939

theorem tailTrace_174710 : CollatzResearch.WordTrace tailWord_174710 prefixEnd_174710 2215066793755967407939 := by
  unfold tailWord_174710
  simp only [CollatzResearch.WordTrace]
  refine ⟨398262324816436433598599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4248131464708655291718389 398262324816436433598599)
  ·
    refine ⟨597393487224654650397899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 398262324816436433598599 597393487224654650397899)
    ·
      refine ⟨896090230836981975596849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 597393487224654650397899 896090230836981975596849)
      ·
        refine ⟨672067673127736481697637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 896090230836981975596849 672067673127736481697637)
        ·
          refine ⟨126012688711450590318307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 672067673127736481697637 126012688711450590318307)
          ·
            refine ⟨189019033067175885477461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126012688711450590318307 189019033067175885477461)
            ·
              refine ⟨2215066793755967407939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 189019033067175885477461 2215066793755967407939)
              ·
                rfl

theorem cell22_174710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 8].length) (baseStart_174710 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_174710 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_174710 prefixEnd_174710 := by exact prefixLift 174710
  have htrace : WordTrace (prefixWord ++ tailWord_174710) baseStart_174710 baseEnd_174710 := by
    simpa [prefixWord, tailWord_174710, baseEnd_174710] using wordTrace_append hprefix tailTrace_174710
  have hstable : (prefixWord ++ tailWord_174710).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174710).length < 2 ^ (prefixWord ++ tailWord_174710).sum := by decide
  have hdescent : baseEnd_174710 < baseStart_174710 := by decide
  rcases family_descends (prefixWord ++ tailWord_174710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174721 : List Nat := [1, 2, 4, 2, 1, 1, 1, 3, 7]
def baseStart_174721 : Nat := 118140960795 + 174721 * 2 ^ 59
def prefixEnd_174721 : Nat := 4983230072969 + 3 ^ 40 * 174721 * 2
def baseEnd_174721 : Nat := 19936856318736919329773

theorem tailTrace_174721 : CollatzResearch.WordTrace tailWord_174721 prefixEnd_174721 19936856318736919329773 := by
  unfold tailWord_174721
  simp only [CollatzResearch.WordTrace]
  refine ⟨6372598400023131816228017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4248398933348754544152011 6372598400023131816228017)
  ·
    refine ⟨4779448800017348862171013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6372598400023131816228017 4779448800017348862171013)
    ·
      refine ⟨896146650003252911657065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4779448800017348862171013 896146650003252911657065)
      ·
        refine ⟨672109987502439683742799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 896146650003252911657065 672109987502439683742799)
        ·
          refine ⟨1008164981253659525614199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 672109987502439683742799 1008164981253659525614199)
          ·
            refine ⟨1512247471880489288421299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1008164981253659525614199 1512247471880489288421299)
            ·
              refine ⟨2268371207820733932631949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1512247471880489288421299 2268371207820733932631949)
              ·
                refine ⟨850639202932775224736981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2268371207820733932631949 850639202932775224736981)
                ·
                  refine ⟨19936856318736919329773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 850639202932775224736981 19936856318736919329773)
                  ·
                    rfl

theorem cell22_174721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 3, 7].length) (baseStart_174721 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_174721 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_174721 prefixEnd_174721 := by exact prefixLift 174721
  have htrace : WordTrace (prefixWord ++ tailWord_174721) baseStart_174721 baseEnd_174721 := by
    simpa [prefixWord, tailWord_174721, baseEnd_174721] using wordTrace_append hprefix tailTrace_174721
  have hstable : (prefixWord ++ tailWord_174721).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174721).length < 2 ^ (prefixWord ++ tailWord_174721).sum := by decide
  have hdescent : baseEnd_174721 < baseStart_174721 := by decide
  rcases family_descends (prefixWord ++ tailWord_174721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174725 : List Nat := [1, 3, 1, 1, 4, 4, 1, 1, 3, 3]
def baseStart_174725 : Nat := 118140960795 + 174725 * 2 ^ 59
def prefixEnd_174725 : Nat := 4983230072969 + 3 ^ 40 * 174725 * 2
def baseEnd_174725 : Nat := 59811938237956080889307

theorem tailTrace_174725 : CollatzResearch.WordTrace tailWord_174725 prefixEnd_174725 59811938237956080889307 := by
  unfold tailWord_174725
  simp only [CollatzResearch.WordTrace]
  refine ⟨6372744292008640499373629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4248496194672426999582419 6372744292008640499373629)
  ·
    refine ⟨2389779109503240187265111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6372744292008640499373629 2389779109503240187265111)
    ·
      refine ⟨3584668664254860280897667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2389779109503240187265111 3584668664254860280897667)
      ·
        refine ⟨5377002996382290421346501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3584668664254860280897667 5377002996382290421346501)
        ·
          refine ⟨1008188061821679454002469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5377002996382290421346501 1008188061821679454002469)
          ·
            refine ⟨189035261591564897625463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1008188061821679454002469 189035261591564897625463)
            ·
              refine ⟨283552892387347346438195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 189035261591564897625463 283552892387347346438195)
              ·
                refine ⟨425329338581021019657293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 283552892387347346438195 425329338581021019657293)
                ·
                  refine ⟨159498501967882882371485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 425329338581021019657293 159498501967882882371485)
                  ·
                    refine ⟨59811938237956080889307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 159498501967882882371485 59811938237956080889307)
                    ·
                      rfl

theorem cell22_174725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 1, 1, 3, 3].length) (baseStart_174725 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_174725 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_174725 prefixEnd_174725 := by exact prefixLift 174725
  have htrace : WordTrace (prefixWord ++ tailWord_174725) baseStart_174725 baseEnd_174725 := by
    simpa [prefixWord, tailWord_174725, baseEnd_174725] using wordTrace_append hprefix tailTrace_174725
  have hstable : (prefixWord ++ tailWord_174725).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174725).length < 2 ^ (prefixWord ++ tailWord_174725).sum := by decide
  have hdescent : baseEnd_174725 < baseStart_174725 := by decide
  rcases family_descends (prefixWord ++ tailWord_174725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174798 : List Nat := [4, 1, 1, 1, 3, 2, 1, 3, 1, 5]
def baseStart_174798 : Nat := 118140960795 + 174798 * 2 ^ 59
def prefixEnd_174798 : Nat := 4983230072969 + 3 ^ 40 * 174798 * 2
def baseEnd_174798 : Nat := 59836927629808223814083

theorem tailTrace_174798 : CollatzResearch.WordTrace tailWord_174798 prefixEnd_174798 59836927629808223814083 := by
  unfold tailWord_174798
  simp only [CollatzResearch.WordTrace]
  refine ⟨796925852593021745847631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4250271213829449311187365 796925852593021745847631)
  ·
    refine ⟨1195388778889532618771447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 796925852593021745847631 1195388778889532618771447)
    ·
      refine ⟨1793083168334298928157171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1195388778889532618771447 1793083168334298928157171)
      ·
        refine ⟨2689624752501448392235757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1793083168334298928157171 2689624752501448392235757)
        ·
          refine ⟨1008609282188043147088409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2689624752501448392235757 1008609282188043147088409)
          ·
            refine ⟨756456961641032360316307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1008609282188043147088409 756456961641032360316307)
            ·
              refine ⟨1134685442461548540474461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 756456961641032360316307 1134685442461548540474461)
              ·
                refine ⟨425507040923080702677923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1134685442461548540474461 425507040923080702677923)
                ·
                  refine ⟨638260561384621054016885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 425507040923080702677923 638260561384621054016885)
                  ·
                    refine ⟨59836927629808223814083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 638260561384621054016885 59836927629808223814083)
                    ·
                      rfl

theorem cell22_174798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 3, 1, 5].length) (baseStart_174798 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_174798 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_174798 prefixEnd_174798 := by exact prefixLift 174798
  have htrace : WordTrace (prefixWord ++ tailWord_174798) baseStart_174798 baseEnd_174798 := by
    simpa [prefixWord, tailWord_174798, baseEnd_174798] using wordTrace_append hprefix tailTrace_174798
  have hstable : (prefixWord ++ tailWord_174798).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174798).length < 2 ^ (prefixWord ++ tailWord_174798).sum := by decide
  have hdescent : baseEnd_174798 < baseStart_174798 := by decide
  rcases family_descends (prefixWord ++ tailWord_174798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174841 : List Nat := [1, 2, 1, 3, 1, 1, 1, 3, 1, 8]
def baseStart_174841 : Nat := 118140960795 + 174841 * 2 ^ 59
def prefixEnd_174841 : Nat := 4983230072969 + 3 ^ 40 * 174841 * 2
def baseEnd_174841 : Nat := 59851647408570444988951

theorem tailTrace_174841 : CollatzResearch.WordTrace tailWord_174841 prefixEnd_174841 59851647408570444988951 := by
  unfold tailWord_174841
  simp only [CollatzResearch.WordTrace]
  refine ⟨6376975159588392310596377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4251316773058928207064251 6376975159588392310596377)
  ·
    refine ⟨4782731369691294232947283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6376975159588392310596377 4782731369691294232947283)
    ·
      refine ⟨7174097054536941349420925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4782731369691294232947283 7174097054536941349420925)
      ·
        refine ⟨2690286395451353006032847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7174097054536941349420925 2690286395451353006032847)
        ·
          refine ⟨4035429593177029509049271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2690286395451353006032847 4035429593177029509049271)
          ·
            refine ⟨6053144389765544263573907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4035429593177029509049271 6053144389765544263573907)
            ·
              refine ⟨9079716584648316395360861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6053144389765544263573907 9079716584648316395360861)
              ·
                refine ⟨3404893719243118648260323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9079716584648316395360861 3404893719243118648260323)
                ·
                  refine ⟨5107340578864677972390485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3404893719243118648260323 5107340578864677972390485)
                  ·
                    refine ⟨59851647408570444988951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 5107340578864677972390485 59851647408570444988951)
                    ·
                      rfl

theorem cell22_174841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 3, 1, 8].length) (baseStart_174841 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_174841 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_174841 prefixEnd_174841 := by exact prefixLift 174841
  have htrace : WordTrace (prefixWord ++ tailWord_174841) baseStart_174841 baseEnd_174841 := by
    simpa [prefixWord, tailWord_174841, baseEnd_174841] using wordTrace_append hprefix tailTrace_174841
  have hstable : (prefixWord ++ tailWord_174841).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174841).length < 2 ^ (prefixWord ++ tailWord_174841).sum := by decide
  have hdescent : baseEnd_174841 < baseStart_174841 := by decide
  rcases family_descends (prefixWord ++ tailWord_174841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174894 : List Nat := [4, 1, 3, 2, 1, 3, 1, 1, 3, 3]
def baseStart_174894 : Nat := 118140960795 + 174894 * 2 ^ 59
def prefixEnd_174894 : Nat := 4983230072969 + 3 ^ 40 * 174894 * 2
def baseEnd_174894 : Nat := 59869790391695973413789

theorem tailTrace_174894 : CollatzResearch.WordTrace tailWord_174894 prefixEnd_174894 59869790391695973413789 := by
  unfold tailWord_174894
  simp only [CollatzResearch.WordTrace]
  refine ⟨797363528549547795284467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4252605485597588241517157 797363528549547795284467)
  ·
    refine ⟨1196045292824321692926701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 797363528549547795284467 1196045292824321692926701)
    ·
      refine ⟨448516984809120634847513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1196045292824321692926701 448516984809120634847513)
      ·
        refine ⟨336387738606840476135635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 448516984809120634847513 336387738606840476135635)
        ·
          refine ⟨504581607910260714203453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 336387738606840476135635 504581607910260714203453)
          ·
            refine ⟨189218102966347767826295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 504581607910260714203453 189218102966347767826295)
            ·
              refine ⟨283827154449521651739443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 189218102966347767826295 283827154449521651739443)
              ·
                refine ⟨425740731674282477609165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 283827154449521651739443 425740731674282477609165)
                ·
                  refine ⟨159652774377855929103437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 425740731674282477609165 159652774377855929103437)
                  ·
                    refine ⟨59869790391695973413789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 159652774377855929103437 59869790391695973413789)
                    ·
                      rfl

theorem cell22_174894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 1, 1, 3, 3].length) (baseStart_174894 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_174894 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_174894 prefixEnd_174894 := by exact prefixLift 174894
  have htrace : WordTrace (prefixWord ++ tailWord_174894) baseStart_174894 baseEnd_174894 := by
    simpa [prefixWord, tailWord_174894, baseEnd_174894] using wordTrace_append hprefix tailTrace_174894
  have hstable : (prefixWord ++ tailWord_174894).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174894).length < 2 ^ (prefixWord ++ tailWord_174894).sum := by decide
  have hdescent : baseEnd_174894 < baseStart_174894 := by decide
  rcases family_descends (prefixWord ++ tailWord_174894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174903 : List Nat := [1, 1, 3, 1, 2, 1, 4, 2, 3, 4]
def baseStart_174903 : Nat := 118140960795 + 174903 * 2 ^ 59
def prefixEnd_174903 : Nat := 4983230072969 + 3 ^ 40 * 174903 * 2
def baseEnd_174903 : Nat := 59872871275622949938761

theorem tailTrace_174903 : CollatzResearch.WordTrace tailWord_174903 prefixEnd_174903 59872871275622949938761 := by
  unfold tailWord_174903
  simp only [CollatzResearch.WordTrace]
  refine ⟨6379236485363776899353363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4252824323575851266235575 6379236485363776899353363)
  ·
    refine ⟨9568854728045665349030045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6379236485363776899353363 9568854728045665349030045)
    ·
      refine ⟨3588320523017124505886267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9568854728045665349030045 3588320523017124505886267)
      ·
        refine ⟨5382480784525686758829401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3588320523017124505886267 5382480784525686758829401)
        ·
          refine ⟨4036860588394265069122051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5382480784525686758829401 4036860588394265069122051)
          ·
            refine ⟨6055290882591397603683077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4036860588394265069122051 6055290882591397603683077)
            ·
              refine ⟨1135367040485887050690577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6055290882591397603683077 1135367040485887050690577)
              ·
                refine ⟨851525280364415288017933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1135367040485887050690577 851525280364415288017933)
                ·
                  refine ⟨319321980136655733006725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 851525280364415288017933 319321980136655733006725)
                  ·
                    refine ⟨59872871275622949938761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 319321980136655733006725 59872871275622949938761)
                    ·
                      rfl

theorem cell22_174903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 2, 3, 4].length) (baseStart_174903 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_174903 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_174903 prefixEnd_174903 := by exact prefixLift 174903
  have htrace : WordTrace (prefixWord ++ tailWord_174903) baseStart_174903 baseEnd_174903 := by
    simpa [prefixWord, tailWord_174903, baseEnd_174903] using wordTrace_append hprefix tailTrace_174903
  have hstable : (prefixWord ++ tailWord_174903).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174903).length < 2 ^ (prefixWord ++ tailWord_174903).sum := by decide
  have hdescent : baseEnd_174903 < baseStart_174903 := by decide
  rcases family_descends (prefixWord ++ tailWord_174903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174937 : List Nat := [1, 2, 1, 2, 2, 5, 3, 1, 1, 4]
def baseStart_174937 : Nat := 118140960795 + 174937 * 2 ^ 59
def prefixEnd_174937 : Nat := 4983230072969 + 3 ^ 40 * 174937 * 2
def baseEnd_174937 : Nat := 59884510170458194588657

theorem tailTrace_174937 : CollatzResearch.WordTrace tailWord_174937 prefixEnd_174937 59884510170458194588657 := by
  unfold tailWord_174937
  simp only [CollatzResearch.WordTrace]
  refine ⟨6380476567240600706091065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4253651044827067137394043 6380476567240600706091065)
  ·
    refine ⟨4785357425430450529568299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6380476567240600706091065 4785357425430450529568299)
    ·
      refine ⟨7178036138145675794352449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4785357425430450529568299 7178036138145675794352449)
      ·
        refine ⟨5383527103609256845764337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7178036138145675794352449 5383527103609256845764337)
        ·
          refine ⟨4037645327706942634323253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5383527103609256845764337 4037645327706942634323253)
          ·
            refine ⟨378529249472525871967805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4037645327706942634323253 378529249472525871967805)
            ·
              refine ⟨141948468552197201987927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 378529249472525871967805 141948468552197201987927)
              ·
                refine ⟨212922702828295802981891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 141948468552197201987927 212922702828295802981891)
                ·
                  refine ⟨319384054242443704472837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 212922702828295802981891 319384054242443704472837)
                  ·
                    refine ⟨59884510170458194588657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 319384054242443704472837 59884510170458194588657)
                    ·
                      rfl

theorem cell22_174937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 3, 1, 1, 4].length) (baseStart_174937 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_174937 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_174937 prefixEnd_174937 := by exact prefixLift 174937
  have htrace : WordTrace (prefixWord ++ tailWord_174937) baseStart_174937 baseEnd_174937 := by
    simpa [prefixWord, tailWord_174937, baseEnd_174937] using wordTrace_append hprefix tailTrace_174937
  have hstable : (prefixWord ++ tailWord_174937).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174937).length < 2 ^ (prefixWord ++ tailWord_174937).sum := by decide
  have hdescent : baseEnd_174937 < baseStart_174937 := by decide
  rcases family_descends (prefixWord ++ tailWord_174937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174952 : List Nat := [2, 1, 4, 2, 1, 3, 1, 4, 4]
def baseStart_174952 : Nat := 118140960795 + 174952 * 2 ^ 59
def prefixEnd_174952 : Nat := 4983230072969 + 3 ^ 40 * 174952 * 2
def baseEnd_174952 : Nat := 19963214992334385154537

theorem tailTrace_174952 : CollatzResearch.WordTrace tailWord_174952 prefixEnd_174952 19963214992334385154537 := by
  unfold tailWord_174952
  simp only [CollatzResearch.WordTrace]
  refine ⟨3190511831093129133943555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4254015774790838845258073 3190511831093129133943555)
  ·
    refine ⟨4785767746639693700915333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3190511831093129133943555 4785767746639693700915333)
    ·
      refine ⟨897331452494942568921625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4785767746639693700915333 897331452494942568921625)
      ·
        refine ⟨672998589371206926691219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 897331452494942568921625 672998589371206926691219)
        ·
          refine ⟨1009497884056810390036829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 672998589371206926691219 1009497884056810390036829)
          ·
            refine ⟨378561706521303896263811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1009497884056810390036829 378561706521303896263811)
            ·
              refine ⟨567842559781955844395717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 378561706521303896263811 567842559781955844395717)
              ·
                refine ⟨106470479959116720824197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 567842559781955844395717 106470479959116720824197)
                ·
                  refine ⟨19963214992334385154537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 106470479959116720824197 19963214992334385154537)
                  ·
                    rfl

theorem cell22_174952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 1, 4, 4].length) (baseStart_174952 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_174952 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_174952 prefixEnd_174952 := by exact prefixLift 174952
  have htrace : WordTrace (prefixWord ++ tailWord_174952) baseStart_174952 baseEnd_174952 := by
    simpa [prefixWord, tailWord_174952, baseEnd_174952] using wordTrace_append hprefix tailTrace_174952
  have hstable : (prefixWord ++ tailWord_174952).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174952).length < 2 ^ (prefixWord ++ tailWord_174952).sum := by decide
  have hdescent : baseEnd_174952 < baseStart_174952 := by decide
  rcases family_descends (prefixWord ++ tailWord_174952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174963 : List Nat := [1, 1, 1, 2, 2, 1, 7, 7]
def baseStart_174963 : Nat := 118140960795 + 174963 * 2 ^ 59
def prefixEnd_174963 : Nat := 4983230072969 + 3 ^ 40 * 174963 * 2
def baseEnd_174963 : Nat := 6654823389089199270953

theorem tailTrace_174963 : CollatzResearch.WordTrace tailWord_174963 prefixEnd_174963 6654823389089199270953 := by
  unfold tailWord_174963
  simp only [CollatzResearch.WordTrace]
  refine ⟨6381424865146407146537543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4254283243430938097691695 6381424865146407146537543)
  ·
    refine ⟨9572137297719610719806315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6381424865146407146537543 9572137297719610719806315)
    ·
      refine ⟨14358205946579416079709473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9572137297719610719806315 14358205946579416079709473)
      ·
        refine ⟨10768654459934562059782105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14358205946579416079709473 10768654459934562059782105)
        ·
          refine ⟨8076490844950921544836579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10768654459934562059782105 8076490844950921544836579)
          ·
            refine ⟨12114736267426382317254869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8076490844950921544836579 12114736267426382317254869)
            ·
              refine ⟨283939131267805835560661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 12114736267426382317254869 283939131267805835560661)
              ·
                refine ⟨6654823389089199270953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 283939131267805835560661 6654823389089199270953)
                ·
                  rfl

theorem cell22_174963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 7, 7].length) (baseStart_174963 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_174963 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_174963 prefixEnd_174963 := by exact prefixLift 174963
  have htrace : WordTrace (prefixWord ++ tailWord_174963) baseStart_174963 baseEnd_174963 := by
    simpa [prefixWord, tailWord_174963, baseEnd_174963] using wordTrace_append hprefix tailTrace_174963
  have hstable : (prefixWord ++ tailWord_174963).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174963).length < 2 ^ (prefixWord ++ tailWord_174963).sum := by decide
  have hdescent : baseEnd_174963 < baseStart_174963 := by decide
  rcases family_descends (prefixWord ++ tailWord_174963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175012 : List Nat := [2, 3, 1, 2, 1, 2, 4, 1, 3, 3]
def baseStart_175012 : Nat := 118140960795 + 175012 * 2 ^ 59
def prefixEnd_175012 : Nat := 4983230072969 + 3 ^ 40 * 175012 * 2
def baseEnd_175012 : Nat := 59910184203182998963427

theorem tailTrace_175012 : CollatzResearch.WordTrace tailWord_175012 prefixEnd_175012 59910184203182998963427 := by
  unfold tailWord_175012
  simp only [CollatzResearch.WordTrace]
  refine ⟨3191606020984444257535645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4255474694645925676714193 3191606020984444257535645)
  ·
    refine ⟨1196852257869166596575867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3191606020984444257535645 1196852257869166596575867)
    ·
      refine ⟨1795278386803749894863801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1196852257869166596575867 1795278386803749894863801)
      ·
        refine ⟨1346458790102812421147851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1795278386803749894863801 1346458790102812421147851)
        ·
          refine ⟨2019688185154218631721777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1346458790102812421147851 2019688185154218631721777)
          ·
            refine ⟨1514766138865663973791333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2019688185154218631721777 1514766138865663973791333)
            ·
              refine ⟨284018651037311995085875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1514766138865663973791333 284018651037311995085875)
              ·
                refine ⟨426027976555967992628813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 284018651037311995085875 426027976555967992628813)
                ·
                  refine ⟨159760491208487997235805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 426027976555967992628813 159760491208487997235805)
                  ·
                    refine ⟨59910184203182998963427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 159760491208487997235805 59910184203182998963427)
                    ·
                      rfl

theorem cell22_175012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 4, 1, 3, 3].length) (baseStart_175012 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_175012 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_175012 prefixEnd_175012 := by exact prefixLift 175012
  have htrace : WordTrace (prefixWord ++ tailWord_175012) baseStart_175012 baseEnd_175012 := by
    simpa [prefixWord, tailWord_175012, baseEnd_175012] using wordTrace_append hprefix tailTrace_175012
  have hstable : (prefixWord ++ tailWord_175012).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175012).length < 2 ^ (prefixWord ++ tailWord_175012).sum := by decide
  have hdescent : baseEnd_175012 < baseStart_175012 := by decide
  rcases family_descends (prefixWord ++ tailWord_175012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175023 : List Nat := [1, 1, 2, 1, 2, 2, 2, 3, 1, 7]
def baseStart_175023 : Nat := 118140960795 + 175023 * 2 ^ 59
def prefixEnd_175023 : Nat := 4983230072969 + 3 ^ 40 * 175023 * 2
def baseEnd_175023 : Nat := 59913949727982636938393

theorem tailTrace_175023 : CollatzResearch.WordTrace tailWord_175023 prefixEnd_175023 59913949727982636938393 := by
  unfold tailWord_175023
  simp only [CollatzResearch.WordTrace]
  refine ⟨6383613244929037393721723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4255742163286024929147815 6383613244929037393721723)
  ·
    refine ⟨9575419867393556090582585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6383613244929037393721723 9575419867393556090582585)
    ·
      refine ⟨7181564900545167067936939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9575419867393556090582585 7181564900545167067936939)
      ·
        refine ⟨10772347350817750601905409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7181564900545167067936939 10772347350817750601905409)
        ·
          refine ⟨8079260513113312951429057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10772347350817750601905409 8079260513113312951429057)
          ·
            refine ⟨6059445384834984713571793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8079260513113312951429057 6059445384834984713571793)
            ·
              refine ⟨4544584038626238535178845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6059445384834984713571793 4544584038626238535178845)
              ·
                refine ⟨1704219014484839450692067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4544584038626238535178845 1704219014484839450692067)
                ·
                  refine ⟨2556328521727259176038101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1704219014484839450692067 2556328521727259176038101)
                  ·
                    refine ⟨59913949727982636938393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2556328521727259176038101 59913949727982636938393)
                    ·
                      rfl

theorem cell22_175023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 3, 1, 7].length) (baseStart_175023 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_175023 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_175023 prefixEnd_175023 := by exact prefixLift 175023
  have htrace : WordTrace (prefixWord ++ tailWord_175023) baseStart_175023 baseEnd_175023 := by
    simpa [prefixWord, tailWord_175023, baseEnd_175023] using wordTrace_append hprefix tailTrace_175023
  have hstable : (prefixWord ++ tailWord_175023).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175023).length < 2 ^ (prefixWord ++ tailWord_175023).sum := by decide
  have hdescent : baseEnd_175023 < baseStart_175023 := by decide
  rcases family_descends (prefixWord ++ tailWord_175023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175089 : List Nat := [1, 2, 2, 2, 4, 3, 1, 2, 1, 4]
def baseStart_175089 : Nat := 118140960795 + 175089 * 2 ^ 59
def prefixEnd_175089 : Nat := 4983230072969 + 3 ^ 40 * 175089 * 2
def baseEnd_175089 : Nat := 59936542876780464788191

theorem tailTrace_175089 : CollatzResearch.WordTrace tailWord_175089 prefixEnd_175089 59936542876780464788191 := by
  unfold tailWord_175089
  simp only [CollatzResearch.WordTrace]
  refine ⟨6386020462689930665624321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4257346975126620443749547 6386020462689930665624321)
  ·
    refine ⟨4789515347017447999218241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6386020462689930665624321 4789515347017447999218241)
    ·
      refine ⟨3592136510263085999413681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4789515347017447999218241 3592136510263085999413681)
      ·
        refine ⟨2694102382697314499560261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3592136510263085999413681 2694102382697314499560261)
        ·
          refine ⟨505144196755746468667549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2694102382697314499560261 505144196755746468667549)
          ·
            refine ⟨189429073783404925750331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 505144196755746468667549 189429073783404925750331)
            ·
              refine ⟨284143610675107388625497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 189429073783404925750331 284143610675107388625497)
              ·
                refine ⟨213107708006330541469123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 284143610675107388625497 213107708006330541469123)
                ·
                  refine ⟨319661562009495812203685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 213107708006330541469123 319661562009495812203685)
                  ·
                    refine ⟨59936542876780464788191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 319661562009495812203685 59936542876780464788191)
                    ·
                      rfl

theorem cell22_175089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 1, 2, 1, 4].length) (baseStart_175089 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_175089 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_175089 prefixEnd_175089 := by exact prefixLift 175089
  have htrace : WordTrace (prefixWord ++ tailWord_175089) baseStart_175089 baseEnd_175089 := by
    simpa [prefixWord, tailWord_175089, baseEnd_175089] using wordTrace_append hprefix tailTrace_175089
  have hstable : (prefixWord ++ tailWord_175089).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175089).length < 2 ^ (prefixWord ++ tailWord_175089).sum := by decide
  have hdescent : baseEnd_175089 < baseStart_175089 := by decide
  rcases family_descends (prefixWord ++ tailWord_175089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175147 : List Nat := [1, 1, 1, 1, 2, 1, 7, 2, 3, 3]
def baseStart_175147 : Nat := 118140960795 + 175147 * 2 ^ 59
def prefixEnd_175147 : Nat := 4983230072969 + 3 ^ 40 * 175147 * 2
def baseEnd_175147 : Nat := 59956397462087646838013

theorem tailTrace_175147 : CollatzResearch.WordTrace tailWord_175147 prefixEnd_175147 59956397462087646838013 := by
  unfold tailWord_175147
  simp only [CollatzResearch.WordTrace]
  refine ⟨6388135896479806571235695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4258757264319871047490463 6388135896479806571235695)
  ·
    refine ⟨9582203844719709856853543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6388135896479806571235695 9582203844719709856853543)
    ·
      refine ⟨14373305767079564785280315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9582203844719709856853543 14373305767079564785280315)
      ·
        refine ⟨21559958650619347177920473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14373305767079564785280315 21559958650619347177920473)
        ·
          refine ⟨16169968987964510383440355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21559958650619347177920473 16169968987964510383440355)
          ·
            refine ⟨24254953481946765575160533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16169968987964510383440355 24254953481946765575160533)
            ·
              refine ⟨568475472233127318167825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 24254953481946765575160533 568475472233127318167825)
              ·
                refine ⟨426356604174845488625869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 568475472233127318167825 426356604174845488625869)
                ·
                  refine ⟨159883726565567058234701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 426356604174845488625869 159883726565567058234701)
                  ·
                    refine ⟨59956397462087646838013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 159883726565567058234701 59956397462087646838013)
                    ·
                      rfl

theorem cell22_175147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 7, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 7, 2, 3, 3].length) (baseStart_175147 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_175147 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_175147 prefixEnd_175147 := by exact prefixLift 175147
  have htrace : WordTrace (prefixWord ++ tailWord_175147) baseStart_175147 baseEnd_175147 := by
    simpa [prefixWord, tailWord_175147, baseEnd_175147] using wordTrace_append hprefix tailTrace_175147
  have hstable : (prefixWord ++ tailWord_175147).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175147).length < 2 ^ (prefixWord ++ tailWord_175147).sum := by decide
  have hdescent : baseEnd_175147 < baseStart_175147 := by decide
  rcases family_descends (prefixWord ++ tailWord_175147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175181 : List Nat := [1, 6, 1, 1, 1, 3, 2, 1, 3, 3]
def baseStart_175181 : Nat := 118140960795 + 175181 * 2 ^ 59
def prefixEnd_175181 : Nat := 4983230072969 + 3 ^ 40 * 175181 * 2
def baseEnd_175181 : Nat := 59968036356922891487909

theorem tailTrace_175181 : CollatzResearch.WordTrace tailWord_175181 prefixEnd_175181 59968036356922891487909 := by
  unfold tailWord_175181
  simp only [CollatzResearch.WordTrace]
  refine ⟨6389375978356630377973397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4259583985571086918648931 6389375978356630377973397)
  ·
    refine ⟨299501998985467048967503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 6389375978356630377973397 299501998985467048967503)
    ·
      refine ⟨449252998478200573451255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 299501998985467048967503 449252998478200573451255)
      ·
        refine ⟨673879497717300860176883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 449252998478200573451255 673879497717300860176883)
        ·
          refine ⟨1010819246575951290265325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 673879497717300860176883 1010819246575951290265325)
          ·
            refine ⟨379057217465981733849497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1010819246575951290265325 379057217465981733849497)
            ·
              refine ⟨284292913099486300387123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 379057217465981733849497 284292913099486300387123)
              ·
                refine ⟨426439369649229450580685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 284292913099486300387123 426439369649229450580685)
                ·
                  refine ⟨159914763618461043967757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 426439369649229450580685 159914763618461043967757)
                  ·
                    refine ⟨59968036356922891487909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 159914763618461043967757 59968036356922891487909)
                    ·
                      rfl

theorem cell22_175181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 2, 1, 3, 3].length) (baseStart_175181 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_175181 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_175181 prefixEnd_175181 := by exact prefixLift 175181
  have htrace : WordTrace (prefixWord ++ tailWord_175181) baseStart_175181 baseEnd_175181 := by
    simpa [prefixWord, tailWord_175181, baseEnd_175181] using wordTrace_append hprefix tailTrace_175181
  have hstable : (prefixWord ++ tailWord_175181).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175181).length < 2 ^ (prefixWord ++ tailWord_175181).sum := by decide
  have hdescent : baseEnd_175181 < baseStart_175181 := by decide
  rcases family_descends (prefixWord ++ tailWord_175181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175198 : List Nat := [4, 4, 1, 1, 1, 1, 2, 2, 3, 3]
def baseStart_175198 : Nat := 118140960795 + 175198 * 2 ^ 59
def prefixEnd_175198 : Nat := 4983230072969 + 3 ^ 40 * 175198 * 2
def baseEnd_175198 : Nat := 59973855804340513812857

theorem tailTrace_175198 : CollatzResearch.WordTrace tailWord_175198 prefixEnd_175198 59973855804340513812857 := by
  unfold tailWord_175198
  simp only [CollatzResearch.WordTrace]
  refine ⟨798749502411880285167781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4259997346196694854228165 798749502411880285167781)
  ·
    refine ⟨149765531702227553468959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 798749502411880285167781 149765531702227553468959)
    ·
      refine ⟨224648297553341330203439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149765531702227553468959 224648297553341330203439)
      ·
        refine ⟨336972446330011995305159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 224648297553341330203439 336972446330011995305159)
        ·
          refine ⟨505458669495017992957739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 336972446330011995305159 505458669495017992957739)
          ·
            refine ⟨758188004242526989436609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 505458669495017992957739 758188004242526989436609)
            ·
              refine ⟨568641003181895242077457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 758188004242526989436609 568641003181895242077457)
              ·
                refine ⟨426480752386421431558093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 568641003181895242077457 426480752386421431558093)
                ·
                  refine ⟨159930282144908036834285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 426480752386421431558093 159930282144908036834285)
                  ·
                    refine ⟨59973855804340513812857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 159930282144908036834285 59973855804340513812857)
                    ·
                      rfl

theorem cell22_175198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 2, 2, 3, 3].length) (baseStart_175198 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_175198 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_175198 prefixEnd_175198 := by exact prefixLift 175198
  have htrace : WordTrace (prefixWord ++ tailWord_175198) baseStart_175198 baseEnd_175198 := by
    simpa [prefixWord, tailWord_175198, baseEnd_175198] using wordTrace_append hprefix tailTrace_175198
  have hstable : (prefixWord ++ tailWord_175198).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175198).length < 2 ^ (prefixWord ++ tailWord_175198).sum := by decide
  have hdescent : baseEnd_175198 < baseStart_175198 := by decide
  rcases family_descends (prefixWord ++ tailWord_175198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175269 : List Nat := [1, 3, 1, 2, 1, 5, 2, 1, 2, 4]
def baseStart_175269 : Nat := 118140960795 + 175269 * 2 ^ 59
def prefixEnd_175269 : Nat := 4983230072969 + 3 ^ 40 * 175269 * 2
def baseEnd_175269 : Nat := 59998160555319995287639

theorem tailTrace_175269 : CollatzResearch.WordTrace tailWord_175269 prefixEnd_175269 59998160555319995287639 := by
  unfold tailWord_175269
  simp only [CollatzResearch.WordTrace]
  refine ⟨6392585602037821407176861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4261723734691880938117907 6392585602037821407176861)
  ·
    refine ⟨2397219600764183027691323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6392585602037821407176861 2397219600764183027691323)
    ·
      refine ⟨3595829401146274541536985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2397219600764183027691323 3595829401146274541536985)
      ·
        refine ⟨2696872050859705906152739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3595829401146274541536985 2696872050859705906152739)
        ·
          refine ⟨4045308076289558859229109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2696872050859705906152739 4045308076289558859229109)
          ·
            refine ⟨379247632152146143052729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4045308076289558859229109 379247632152146143052729)
            ·
              refine ⟨284435724114109607289547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 379247632152146143052729 284435724114109607289547)
              ·
                refine ⟨426653586171164410934321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 284435724114109607289547 426653586171164410934321)
                ·
                  refine ⟨319990189628373308200741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 426653586171164410934321 319990189628373308200741)
                  ·
                    refine ⟨59998160555319995287639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 319990189628373308200741 59998160555319995287639)
                    ·
                      rfl

theorem cell22_175269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 2, 1, 2, 4].length) (baseStart_175269 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_175269 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_175269 prefixEnd_175269 := by exact prefixLift 175269
  have htrace : WordTrace (prefixWord ++ tailWord_175269) baseStart_175269 baseEnd_175269 := by
    simpa [prefixWord, tailWord_175269, baseEnd_175269] using wordTrace_append hprefix tailTrace_175269
  have hstable : (prefixWord ++ tailWord_175269).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175269).length < 2 ^ (prefixWord ++ tailWord_175269).sum := by decide
  have hdescent : baseEnd_175269 < baseStart_175269 := by decide
  rcases family_descends (prefixWord ++ tailWord_175269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175284 : List Nat := [2, 5, 3, 12]
def baseStart_175284 : Nat := 118140960795 + 175284 * 2 ^ 59
def prefixEnd_175284 : Nat := 4983230072969 + 3 ^ 40 * 175284 * 2
def baseEnd_175284 : Nat := 82309047135617223817

theorem tailTrace_175284 : CollatzResearch.WordTrace tailWord_175284 prefixEnd_175284 82309047135617223817 := by
  unfold tailWord_175284
  simp only [CollatzResearch.WordTrace]
  refine ⟨3196566348491739484486453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4262088464655652645981937 3196566348491739484486453)
  ·
    refine ⟨299678095171100576670605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3196566348491739484486453 299678095171100576670605)
    ·
      refine ⟨112379285689162716251477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 299678095171100576670605 112379285689162716251477)
      ·
        refine ⟨82309047135617223817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 12 112379285689162716251477 82309047135617223817)
        ·
          rfl

theorem cell22_175284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 12].length) (baseStart_175284 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_175284 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_175284 prefixEnd_175284 := by exact prefixLift 175284
  have htrace : WordTrace (prefixWord ++ tailWord_175284) baseStart_175284 baseEnd_175284 := by
    simpa [prefixWord, tailWord_175284, baseEnd_175284] using wordTrace_append hprefix tailTrace_175284
  have hstable : (prefixWord ++ tailWord_175284).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175284).length < 2 ^ (prefixWord ++ tailWord_175284).sum := by decide
  have hdescent : baseEnd_175284 < baseStart_175284 := by decide
  rcases family_descends (prefixWord ++ tailWord_175284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175318 : List Nat := [5, 2, 1, 2, 2, 1, 3, 6]
def baseStart_175318 : Nat := 118140960795 + 175318 * 2 ^ 59
def prefixEnd_175318 : Nat := 4983230072969 + 3 ^ 40 * 175318 * 2
def baseEnd_175318 : Nat := 6668326028522244534721

theorem tailTrace_175318 : CollatzResearch.WordTrace tailWord_175318 prefixEnd_175318 6668326028522244534721 := by
  unfold tailWord_175318
  simp only [CollatzResearch.WordTrace]
  refine ⟨399648298678768923481913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4262915185906868517140405 399648298678768923481913)
  ·
    refine ⟨299736224009076692611435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 399648298678768923481913 299736224009076692611435)
    ·
      refine ⟨449604336013615038917153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 299736224009076692611435 449604336013615038917153)
      ·
        refine ⟨337203252010211279187865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 449604336013615038917153 337203252010211279187865)
        ·
          refine ⟨252902439007658459390899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 337203252010211279187865 252902439007658459390899)
          ·
            refine ⟨379353658511487689086349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 252902439007658459390899 379353658511487689086349)
            ·
              refine ⟨142257621941807883407381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 379353658511487689086349 142257621941807883407381)
              ·
                refine ⟨6668326028522244534721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 142257621941807883407381 6668326028522244534721)
                ·
                  rfl

theorem cell22_175318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 3, 6].length) (baseStart_175318 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_175318 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_175318 prefixEnd_175318 := by exact prefixLift 175318
  have htrace : WordTrace (prefixWord ++ tailWord_175318) baseStart_175318 baseEnd_175318 := by
    simpa [prefixWord, tailWord_175318, baseEnd_175318] using wordTrace_append hprefix tailTrace_175318
  have hstable : (prefixWord ++ tailWord_175318).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175318).length < 2 ^ (prefixWord ++ tailWord_175318).sum := by decide
  have hdescent : baseEnd_175318 < baseStart_175318 := by decide
  rcases family_descends (prefixWord ++ tailWord_175318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175374 : List Nat := [4, 1, 1, 2, 1, 3, 2, 2, 6]
def baseStart_175374 : Nat := 118140960795 + 175374 * 2 ^ 59
def prefixEnd_175374 : Nat := 4983230072969 + 3 ^ 40 * 175374 * 2
def baseEnd_175374 : Nat := 20011368067044907137439

theorem tailTrace_175374 : CollatzResearch.WordTrace tailWord_175374 prefixEnd_175374 20011368067044907137439 := by
  unfold tailWord_175374
  simp only [CollatzResearch.WordTrace]
  refine ⟨799551908332178042468647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4264276844438282893166117 799551908332178042468647)
  ·
    refine ⟨1199327862498267063702971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 799551908332178042468647 1199327862498267063702971)
    ·
      refine ⟨1798991793747400595554457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1199327862498267063702971 1798991793747400595554457)
      ·
        refine ⟨1349243845310550446665843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1798991793747400595554457 1349243845310550446665843)
        ·
          refine ⟨2023865767965825669998765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1349243845310550446665843 2023865767965825669998765)
          ·
            refine ⟨758949662987184626249537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2023865767965825669998765 758949662987184626249537)
            ·
              refine ⟨569212247240388469687153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 758949662987184626249537 569212247240388469687153)
              ·
                refine ⟨426909185430291352265365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 569212247240388469687153 426909185430291352265365)
                ·
                  refine ⟨20011368067044907137439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 426909185430291352265365 20011368067044907137439)
                  ·
                    rfl

theorem cell22_175374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 2, 2, 6].length) (baseStart_175374 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_175374 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_175374 prefixEnd_175374 := by exact prefixLift 175374
  have htrace : WordTrace (prefixWord ++ tailWord_175374) baseStart_175374 baseEnd_175374 := by
    simpa [prefixWord, tailWord_175374, baseEnd_175374] using wordTrace_append hprefix tailTrace_175374
  have hstable : (prefixWord ++ tailWord_175374).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175374).length < 2 ^ (prefixWord ++ tailWord_175374).sum := by decide
  have hdescent : baseEnd_175374 < baseStart_175374 := by decide
  rcases family_descends (prefixWord ++ tailWord_175374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175423 : List Nat := [1, 1, 2, 2, 4, 2, 4, 1, 2, 3]
def baseStart_175423 : Nat := 118140960795 + 175423 * 2 ^ 59
def prefixEnd_175423 : Nat := 4983230072969 + 3 ^ 40 * 175423 * 2
def baseEnd_175423 : Nat := 60050877902514926937167

theorem tailTrace_175423 : CollatzResearch.WordTrace tailWord_175423 prefixEnd_175423 60050877902514926937167 := by
  unfold tailWord_175423
  simp only [CollatzResearch.WordTrace]
  refine ⟨6398202443479905708282923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4265468295653270472188615 6398202443479905708282923)
  ·
    refine ⟨9597303665219858562424385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6398202443479905708282923 9597303665219858562424385)
    ·
      refine ⟨7197977748914893921818289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9597303665219858562424385 7197977748914893921818289)
      ·
        refine ⟨5398483311686170441363717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7197977748914893921818289 5398483311686170441363717)
        ·
          refine ⟨1012215620941156957755697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5398483311686170441363717 1012215620941156957755697)
          ·
            refine ⟨759161715705867718316773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1012215620941156957755697 759161715705867718316773)
            ·
              refine ⟨142342821694850197184395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 759161715705867718316773 142342821694850197184395)
              ·
                refine ⟨213514232542275295776593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 142342821694850197184395 213514232542275295776593)
                ·
                  refine ⟨160135674406706471832445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 213514232542275295776593 160135674406706471832445)
                  ·
                    refine ⟨60050877902514926937167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 160135674406706471832445 60050877902514926937167)
                    ·
                      rfl

theorem cell22_175423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 4, 1, 2, 3].length) (baseStart_175423 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_175423 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_175423 prefixEnd_175423 := by exact prefixLift 175423
  have htrace : WordTrace (prefixWord ++ tailWord_175423) baseStart_175423 baseEnd_175423 := by
    simpa [prefixWord, tailWord_175423, baseEnd_175423] using wordTrace_append hprefix tailTrace_175423
  have hstable : (prefixWord ++ tailWord_175423).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175423).length < 2 ^ (prefixWord ++ tailWord_175423).sum := by decide
  have hdescent : baseEnd_175423 < baseStart_175423 := by decide
  rcases family_descends (prefixWord ++ tailWord_175423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175453 : List Nat := [1, 4, 5, 1, 1, 10]
def baseStart_175453 : Nat := 118140960795 + 175453 * 2 ^ 59
def prefixEnd_175453 : Nat := 4983230072969 + 3 ^ 40 * 175453 * 2
def baseEnd_175453 : Nat := 741495648340800601075

theorem tailTrace_175453 : CollatzResearch.WordTrace tailWord_175453 prefixEnd_175453 741495648340800601075 := by
  unfold tailWord_175453
  simp only [CollatzResearch.WordTrace]
  refine ⟨6399296633371220831875013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4266197755580813887916675 6399296633371220831875013)
  ·
    refine ⟨1199868118757103905976565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6399296633371220831875013 1199868118757103905976565)
    ·
      refine ⟨112487636133478491185303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1199868118757103905976565 112487636133478491185303)
      ·
        refine ⟨168731454200217736777955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112487636133478491185303 168731454200217736777955)
        ·
          refine ⟨253097181300326605166933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168731454200217736777955 253097181300326605166933)
          ·
            refine ⟨741495648340800601075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 253097181300326605166933 741495648340800601075)
            ·
              rfl

theorem cell22_175453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 10].length) (baseStart_175453 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_175453 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_175453 prefixEnd_175453 := by exact prefixLift 175453
  have htrace : WordTrace (prefixWord ++ tailWord_175453) baseStart_175453 baseEnd_175453 := by
    simpa [prefixWord, tailWord_175453, baseEnd_175453] using wordTrace_append hprefix tailTrace_175453
  have hstable : (prefixWord ++ tailWord_175453).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175453).length < 2 ^ (prefixWord ++ tailWord_175453).sum := by decide
  have hdescent : baseEnd_175453 < baseStart_175453 := by decide
  rcases family_descends (prefixWord ++ tailWord_175453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175470 : List Nat := [4, 1, 2, 4, 2, 1, 1, 7]
def baseStart_175470 : Nat := 118140960795 + 175470 * 2 ^ 59
def prefixEnd_175470 : Nat := 4983230072969 + 3 ^ 40 * 175470 * 2
def baseEnd_175470 : Nat := 6674107440335830112447

theorem tailTrace_175470 : CollatzResearch.WordTrace tailWord_175470 prefixEnd_175470 6674107440335830112447 := by
  unfold tailWord_175470
  simp only [CollatzResearch.WordTrace]
  refine ⟨799989584288704091905483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4266611116206421823495909 799989584288704091905483)
  ·
    refine ⟨1199984376433056137858225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 799989584288704091905483 1199984376433056137858225)
    ·
      refine ⟨899988282324792103393669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1199984376433056137858225 899988282324792103393669)
      ·
        refine ⟨168747802935898519386313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 899988282324792103393669 168747802935898519386313)
        ·
          refine ⟨126560852201923889539735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 168747802935898519386313 126560852201923889539735)
          ·
            refine ⟨189841278302885834309603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126560852201923889539735 189841278302885834309603)
            ·
              refine ⟨284761917454328751464405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 189841278302885834309603 284761917454328751464405)
              ·
                refine ⟨6674107440335830112447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 284761917454328751464405 6674107440335830112447)
                ·
                  rfl

theorem cell22_175470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 1, 7].length) (baseStart_175470 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_175470 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_175470 prefixEnd_175470 := by exact prefixLift 175470
  have htrace : WordTrace (prefixWord ++ tailWord_175470) baseStart_175470 baseEnd_175470 := by
    simpa [prefixWord, tailWord_175470, baseEnd_175470] using wordTrace_append hprefix tailTrace_175470
  have hstable : (prefixWord ++ tailWord_175470).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175470).length < 2 ^ (prefixWord ++ tailWord_175470).sum := by decide
  have hdescent : baseEnd_175470 < baseStart_175470 := by decide
  rcases family_descends (prefixWord ++ tailWord_175470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175479 : List Nat := [1, 1, 3, 1, 1, 2, 5, 1, 2, 5]
def baseStart_175479 : Nat := 118140960795 + 175479 * 2 ^ 59
def prefixEnd_175479 : Nat := 4983230072969 + 3 ^ 40 * 175479 * 2
def baseEnd_175479 : Nat := 60070047846949447536995

theorem tailTrace_175479 : CollatzResearch.WordTrace tailWord_175479 prefixEnd_175479 60070047846949447536995 := by
  unfold tailWord_175479
  simp only [CollatzResearch.WordTrace]
  refine ⟨6400244931277027272321491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4266829954184684848214327 6400244931277027272321491)
  ·
    refine ⟨9600367396915540908482237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6400244931277027272321491 9600367396915540908482237)
    ·
      refine ⟨3600137773843327840680839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9600367396915540908482237 3600137773843327840680839)
      ·
        refine ⟨5400206660764991761021259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3600137773843327840680839 5400206660764991761021259)
        ·
          refine ⟨8100309991147487641531889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5400206660764991761021259 8100309991147487641531889)
          ·
            refine ⟨6075232493360615731148917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8100309991147487641531889 6075232493360615731148917)
            ·
              refine ⟨569553046252557724795211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6075232493360615731148917 569553046252557724795211)
              ·
                refine ⟨854329569378836587192817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 569553046252557724795211 854329569378836587192817)
                ·
                  refine ⟨640747177034127440394613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 854329569378836587192817 640747177034127440394613)
                  ·
                    refine ⟨60070047846949447536995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 640747177034127440394613 60070047846949447536995)
                    ·
                      rfl

theorem cell22_175479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 5, 1, 2, 5].length) (baseStart_175479 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_175479 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_175479 prefixEnd_175479 := by exact prefixLift 175479
  have htrace : WordTrace (prefixWord ++ tailWord_175479) baseStart_175479 baseEnd_175479 := by
    simpa [prefixWord, tailWord_175479, baseEnd_175479] using wordTrace_append hprefix tailTrace_175479
  have hstable : (prefixWord ++ tailWord_175479).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175479).length < 2 ^ (prefixWord ++ tailWord_175479).sum := by decide
  have hdescent : baseEnd_175479 < baseStart_175479 := by decide
  rcases family_descends (prefixWord ++ tailWord_175479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175502 : List Nat := [4, 1, 1, 4, 2, 1, 2, 3, 1, 3]
def baseStart_175502 : Nat := 118140960795 + 175502 * 2 ^ 59
def prefixEnd_175502 : Nat := 4983230072969 + 3 ^ 40 * 175502 * 2
def baseEnd_175502 : Nat := 60077921216985054211925

theorem tailTrace_175502 : CollatzResearch.WordTrace tailWord_175502 prefixEnd_175502 60077921216985054211925 := by
  unfold tailWord_175502
  simp only [CollatzResearch.WordTrace]
  refine ⟨800135476274212775051095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4267389206795801466939173 800135476274212775051095)
  ·
    refine ⟨1200203214411319162576643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 800135476274212775051095 1200203214411319162576643)
    ·
      refine ⟨1800304821616978743864965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1200203214411319162576643 1800304821616978743864965)
      ·
        refine ⟨337557154053183514474681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1800304821616978743864965 337557154053183514474681)
        ·
          refine ⟨253167865539887635856011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 337557154053183514474681 253167865539887635856011)
          ·
            refine ⟨379751798309831453784017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 253167865539887635856011 379751798309831453784017)
            ·
              refine ⟨284813848732373590338013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 379751798309831453784017 284813848732373590338013)
              ·
                refine ⟨106805193274640096376755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 284813848732373590338013 106805193274640096376755)
                ·
                  refine ⟨160207789911960144565133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 106805193274640096376755 160207789911960144565133)
                  ·
                    refine ⟨60077921216985054211925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 160207789911960144565133 60077921216985054211925)
                    ·
                      rfl

theorem cell22_175502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 2, 3, 1, 3].length) (baseStart_175502 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_175502 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_175502 prefixEnd_175502 := by exact prefixLift 175502
  have htrace : WordTrace (prefixWord ++ tailWord_175502) baseStart_175502 baseEnd_175502 := by
    simpa [prefixWord, tailWord_175502, baseEnd_175502] using wordTrace_append hprefix tailTrace_175502
  have hstable : (prefixWord ++ tailWord_175502).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175502).length < 2 ^ (prefixWord ++ tailWord_175502).sum := by decide
  have hdescent : baseEnd_175502 < baseStart_175502 := by decide
  rcases family_descends (prefixWord ++ tailWord_175502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175622 : List Nat := [6, 2, 1, 1, 3, 9]
def baseStart_175622 : Nat := 118140960795 + 175622 * 2 ^ 59
def prefixEnd_175622 : Nat := 4983230072969 + 3 ^ 40 * 175622 * 2
def baseEnd_175622 : Nat := 742209872461046187797

theorem tailTrace_175622 : CollatzResearch.WordTrace tailWord_175622 prefixEnd_175622 742209872461046187797 := by
  unfold tailWord_175622
  simp only [CollatzResearch.WordTrace]
  refine ⟨200170642804967584211785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 4270307046505975129851413 200170642804967584211785)
  ·
    refine ⟨150127982103725688158839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200170642804967584211785 150127982103725688158839)
    ·
      refine ⟨225191973155588532238259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150127982103725688158839 225191973155588532238259)
      ·
        refine ⟨337787959733382798357389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 225191973155588532238259 337787959733382798357389)
        ·
          refine ⟨126670484900018549384021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 337787959733382798357389 126670484900018549384021)
          ·
            refine ⟨742209872461046187797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 126670484900018549384021 742209872461046187797)
            ·
              rfl

theorem cell22_175622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 9].length) (baseStart_175622 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_175622 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_175622 prefixEnd_175622 := by exact prefixLift 175622
  have htrace : WordTrace (prefixWord ++ tailWord_175622) baseStart_175622 baseEnd_175622 := by
    simpa [prefixWord, tailWord_175622, baseEnd_175622] using wordTrace_append hprefix tailTrace_175622
  have hstable : (prefixWord ++ tailWord_175622).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175622).length < 2 ^ (prefixWord ++ tailWord_175622).sum := by decide
  have hdescent : baseEnd_175622 < baseStart_175622 := by decide
  rcases family_descends (prefixWord ++ tailWord_175622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175637 : List Nat := [1, 3, 2, 1, 3, 2, 4, 2, 1, 3]
def baseStart_175637 : Nat := 118140960795 + 175637 * 2 ^ 59
def prefixEnd_175637 : Nat := 4983230072969 + 3 ^ 40 * 175637 * 2
def baseEnd_175637 : Nat := 60124134475889702086511

theorem tailTrace_175637 : CollatzResearch.WordTrace tailWord_175637 prefixEnd_175637 60124134475889702086511 := by
  unfold tailWord_175637
  simp only [CollatzResearch.WordTrace]
  refine ⟨6406007664704620256573165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4270671776469746837715443 6406007664704620256573165)
  ·
    refine ⟨2402252874264232596214937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6406007664704620256573165 2402252874264232596214937)
    ·
      refine ⟨1801689655698174447161203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2402252874264232596214937 1801689655698174447161203)
      ·
        refine ⟨2702534483547261670741805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1801689655698174447161203 2702534483547261670741805)
        ·
          refine ⟨1013450431330223126528177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2702534483547261670741805 1013450431330223126528177)
          ·
            refine ⟨760087823497667344896133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1013450431330223126528177 760087823497667344896133)
            ·
              refine ⟨142516466905812627168025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 760087823497667344896133 142516466905812627168025)
              ·
                refine ⟨106887350179359470376019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 142516466905812627168025 106887350179359470376019)
                ·
                  refine ⟨160331025269039205564029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 106887350179359470376019 160331025269039205564029)
                  ·
                    refine ⟨60124134475889702086511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 160331025269039205564029 60124134475889702086511)
                    ·
                      rfl

theorem cell22_175637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 4, 2, 1, 3].length) (baseStart_175637 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_175637 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_175637 prefixEnd_175637 := by exact prefixLift 175637
  have htrace : WordTrace (prefixWord ++ tailWord_175637) baseStart_175637 baseEnd_175637 := by
    simpa [prefixWord, tailWord_175637, baseEnd_175637] using wordTrace_append hprefix tailTrace_175637
  have hstable : (prefixWord ++ tailWord_175637).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175637).length < 2 ^ (prefixWord ++ tailWord_175637).sum := by decide
  have hdescent : baseEnd_175637 < baseStart_175637 := by decide
  rcases family_descends (prefixWord ++ tailWord_175637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175648 : List Nat := [2, 1, 1, 6, 1, 2, 1, 1, 2, 5]
def baseStart_175648 : Nat := 118140960795 + 175648 * 2 ^ 59
def prefixEnd_175648 : Nat := 4983230072969 + 3 ^ 40 * 175648 * 2
def baseEnd_175648 : Nat := 60127900000689340061477

theorem tailTrace_175648 : CollatzResearch.WordTrace tailWord_175648 prefixEnd_175648 60127900000689340061477 := by
  unfold tailWord_175648
  simp only [CollatzResearch.WordTrace]
  refine ⟨3203204433832384567611799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4270939245109846090149065 3203204433832384567611799)
  ·
    refine ⟨4804806650748576851417699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3203204433832384567611799 4804806650748576851417699)
    ·
      refine ⟨7207209976122865277126549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4804806650748576851417699 7207209976122865277126549)
      ·
        refine ⟨337837967630759309865307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 7207209976122865277126549 337837967630759309865307)
        ·
          refine ⟨506756951446138964797961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 337837967630759309865307 506756951446138964797961)
          ·
            refine ⟨380067713584604223598471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 506756951446138964797961 380067713584604223598471)
            ·
              refine ⟨570101570376906335397707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 380067713584604223598471 570101570376906335397707)
              ·
                refine ⟨855152355565359503096561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 570101570376906335397707 855152355565359503096561)
                ·
                  refine ⟨641364266674019627322421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 855152355565359503096561 641364266674019627322421)
                  ·
                    refine ⟨60127900000689340061477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 641364266674019627322421 60127900000689340061477)
                    ·
                      rfl

theorem cell22_175648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 1, 1, 2, 5].length) (baseStart_175648 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_175648 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_175648 prefixEnd_175648 := by exact prefixLift 175648
  have htrace : WordTrace (prefixWord ++ tailWord_175648) baseStart_175648 baseEnd_175648 := by
    simpa [prefixWord, tailWord_175648, baseEnd_175648] using wordTrace_append hprefix tailTrace_175648
  have hstable : (prefixWord ++ tailWord_175648).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175648).length < 2 ^ (prefixWord ++ tailWord_175648).sum := by decide
  have hdescent : baseEnd_175648 < baseStart_175648 := by decide
  rcases family_descends (prefixWord ++ tailWord_175648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175691 : List Nat := [1, 1, 1, 1, 3, 1, 3, 3, 4, 4]
def baseStart_175691 : Nat := 118140960795 + 175691 * 2 ^ 59
def prefixEnd_175691 : Nat := 4983230072969 + 3 ^ 40 * 175691 * 2
def baseEnd_175691 : Nat := 60142619779451561236345

theorem tailTrace_175691 : CollatzResearch.WordTrace tailWord_175691 prefixEnd_175691 60142619779451561236345 := by
  unfold tailWord_175691
  simp only [CollatzResearch.WordTrace]
  refine ⟨6407977206508987479038927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4271984804339324986025951 6407977206508987479038927)
  ·
    refine ⟨9611965809763481218558391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6407977206508987479038927 9611965809763481218558391)
    ·
      refine ⟨14417948714645221827837587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9611965809763481218558391 14417948714645221827837587)
      ·
        refine ⟨21626923071967832741756381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14417948714645221827837587 21626923071967832741756381)
        ·
          refine ⟨8110096151987937278158643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21626923071967832741756381 8110096151987937278158643)
          ·
            refine ⟨12165144227981905917237965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8110096151987937278158643 12165144227981905917237965)
            ·
              refine ⟨4561929085493214718964237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12165144227981905917237965 4561929085493214718964237)
              ·
                refine ⟨1710723407059955519611589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4561929085493214718964237 1710723407059955519611589)
                ·
                  refine ⟨320760638823741659927173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1710723407059955519611589 320760638823741659927173)
                  ·
                    refine ⟨60142619779451561236345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 320760638823741659927173 60142619779451561236345)
                    ·
                      rfl

theorem cell22_175691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 3, 4, 4].length) (baseStart_175691 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_175691 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_175691 prefixEnd_175691 := by exact prefixLift 175691
  have htrace : WordTrace (prefixWord ++ tailWord_175691) baseStart_175691 baseEnd_175691 := by
    simpa [prefixWord, tailWord_175691, baseEnd_175691] using wordTrace_append hprefix tailTrace_175691
  have hstable : (prefixWord ++ tailWord_175691).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175691).length < 2 ^ (prefixWord ++ tailWord_175691).sum := by decide
  have hdescent : baseEnd_175691 < baseStart_175691 := by decide
  rcases family_descends (prefixWord ++ tailWord_175691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175708 : List Nat := [2, 2, 4, 1, 2, 1, 1, 2, 1, 6]
def baseStart_175708 : Nat := 118140960795 + 175708 * 2 ^ 59
def prefixEnd_175708 : Nat := 4983230072969 + 3 ^ 40 * 175708 * 2
def baseEnd_175708 : Nat := 60148439226869183561293

theorem tailTrace_175708 : CollatzResearch.WordTrace tailWord_175708 prefixEnd_175708 60148439226869183561293 := by
  unfold tailWord_175708
  simp only [CollatzResearch.WordTrace]
  refine ⟨3204298623723699691203889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4272398164964932921605185 3204298623723699691203889)
  ·
    refine ⟨2403223967792774768402917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3204298623723699691203889 2403223967792774768402917)
    ·
      refine ⟨450604493961145269075547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2403223967792774768402917 450604493961145269075547)
      ·
        refine ⟨675906740941717903613321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 450604493961145269075547 675906740941717903613321)
        ·
          refine ⟨506930055706288427709991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 675906740941717903613321 506930055706288427709991)
          ·
            refine ⟨760395083559432641564987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 506930055706288427709991 760395083559432641564987)
            ·
              refine ⟨1140592625339148962347481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 760395083559432641564987 1140592625339148962347481)
              ·
                refine ⟨855444469004361721760611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1140592625339148962347481 855444469004361721760611)
                ·
                  refine ⟨1283166703506542582640917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 855444469004361721760611 1283166703506542582640917)
                  ·
                    refine ⟨60148439226869183561293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1283166703506542582640917 60148439226869183561293)
                    ·
                      rfl

theorem cell22_175708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 2, 1, 6].length) (baseStart_175708 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_175708 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_175708 prefixEnd_175708 := by exact prefixLift 175708
  have htrace : WordTrace (prefixWord ++ tailWord_175708) baseStart_175708 baseEnd_175708 := by
    simpa [prefixWord, tailWord_175708, baseEnd_175708] using wordTrace_append hprefix tailTrace_175708
  have hstable : (prefixWord ++ tailWord_175708).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175708).length < 2 ^ (prefixWord ++ tailWord_175708).sum := by decide
  have hdescent : baseEnd_175708 < baseStart_175708 := by decide
  rcases family_descends (prefixWord ++ tailWord_175708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175806 : List Nat := [4, 2, 1, 1, 2, 4, 2, 2, 1, 3]
def baseStart_175806 : Nat := 118140960795 + 175806 * 2 ^ 59
def prefixEnd_175806 : Nat := 4983230072969 + 3 ^ 40 * 175806 * 2
def baseEnd_175806 : Nat := 60181986629629594610993

theorem tailTrace_175806 : CollatzResearch.WordTrace tailWord_175806 prefixEnd_175806 60181986629629594610993 := by
  unfold tailWord_175806
  simp only [CollatzResearch.WordTrace]
  refine ⟨801521450136545264934409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4274781067394908079650181 801521450136545264934409)
  ·
    refine ⟨601141087602408948700807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 801521450136545264934409 601141087602408948700807)
    ·
      refine ⟨901711631403613423051211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 601141087602408948700807 901711631403613423051211)
      ·
        refine ⟨1352567447105420134576817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 901711631403613423051211 1352567447105420134576817)
        ·
          refine ⟨1014425585329065100932613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1352567447105420134576817 1014425585329065100932613)
          ·
            refine ⟨190204797249199706424865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1014425585329065100932613 190204797249199706424865)
            ·
              refine ⟨142653597936899779818649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 190204797249199706424865 142653597936899779818649)
              ·
                refine ⟨106990198452674834863987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 142653597936899779818649 106990198452674834863987)
                ·
                  refine ⟨160485297679012252295981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 106990198452674834863987 160485297679012252295981)
                  ·
                    refine ⟨60181986629629594610993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 160485297679012252295981 60181986629629594610993)
                    ·
                      rfl

theorem cell22_175806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 2, 2, 1, 3].length) (baseStart_175806 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_175806 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_175806 prefixEnd_175806 := by exact prefixLift 175806
  have htrace : WordTrace (prefixWord ++ tailWord_175806) baseStart_175806 baseEnd_175806 := by
    simpa [prefixWord, tailWord_175806, baseEnd_175806] using wordTrace_append hprefix tailTrace_175806
  have hstable : (prefixWord ++ tailWord_175806).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175806).length < 2 ^ (prefixWord ++ tailWord_175806).sum := by decide
  have hdescent : baseEnd_175806 < baseStart_175806 := by decide
  rcases family_descends (prefixWord ++ tailWord_175806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175845 : List Nat := [1, 3, 1, 4, 1, 1, 2, 2, 4, 3]
def baseStart_175845 : Nat := 118140960795 + 175845 * 2 ^ 59
def prefixEnd_175845 : Nat := 4983230072969 + 3 ^ 40 * 175845 * 2
def baseEnd_175845 : Nat := 60195337126646492885873

theorem tailTrace_175845 : CollatzResearch.WordTrace tailWord_175845 prefixEnd_175845 60195337126646492885873 := by
  unfold tailWord_175845
  simp only [CollatzResearch.WordTrace]
  refine ⟨6413594047951071780144989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4275729365300714520096659 6413594047951071780144989)
  ·
    refine ⟨2405097767981651917554371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6413594047951071780144989 2405097767981651917554371)
    ·
      refine ⟨3607646651972477876331557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2405097767981651917554371 3607646651972477876331557)
      ·
        refine ⟨676433747244839601812167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3607646651972477876331557 676433747244839601812167)
        ·
          refine ⟨1014650620867259402718251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 676433747244839601812167 1014650620867259402718251)
          ·
            refine ⟨1521975931300889104077377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1014650620867259402718251 1521975931300889104077377)
            ·
              refine ⟨1141481948475666828058033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1521975931300889104077377 1141481948475666828058033)
              ·
                refine ⟨856111461356750121043525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1141481948475666828058033 856111461356750121043525)
                ·
                  refine ⟨160520899004390647695661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 856111461356750121043525 160520899004390647695661)
                  ·
                    refine ⟨60195337126646492885873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 160520899004390647695661 60195337126646492885873)
                    ·
                      rfl

theorem cell22_175845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 2, 4, 3].length) (baseStart_175845 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_175845 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_175845 prefixEnd_175845 := by exact prefixLift 175845
  have htrace : WordTrace (prefixWord ++ tailWord_175845) baseStart_175845 baseEnd_175845 := by
    simpa [prefixWord, tailWord_175845, baseEnd_175845] using wordTrace_append hprefix tailTrace_175845
  have hstable : (prefixWord ++ tailWord_175845).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175845).length < 2 ^ (prefixWord ++ tailWord_175845).sum := by decide
  have hdescent : baseEnd_175845 < baseStart_175845 := by decide
  rcases family_descends (prefixWord ++ tailWord_175845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175858 : List Nat := [3, 2, 1, 3, 1, 1, 11]
def baseStart_175858 : Nat := 118140960795 + 175858 * 2 ^ 59
def prefixEnd_175858 : Nat := 4983230072969 + 3 ^ 40 * 175858 * 2
def baseEnd_175858 : Nat := 2229621751567362678179

theorem tailTrace_175858 : CollatzResearch.WordTrace tailWord_175858 prefixEnd_175858 2229621751567362678179 := by
  unfold tailWord_175858
  simp only [CollatzResearch.WordTrace]
  refine ⟨1603517049225993750092057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4276045464602650000245485 1603517049225993750092057)
  ·
    refine ⟨1202637786919495312569043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1603517049225993750092057 1202637786919495312569043)
    ·
      refine ⟨1803956680379242968853565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1202637786919495312569043 1803956680379242968853565)
      ·
        refine ⟨676483755142216113320087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1803956680379242968853565 676483755142216113320087)
        ·
          refine ⟨1014725632713324169980131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 676483755142216113320087 1014725632713324169980131)
          ·
            refine ⟨1522088449069986254970197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1014725632713324169980131 1522088449069986254970197)
            ·
              refine ⟨2229621751567362678179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 1522088449069986254970197 2229621751567362678179)
              ·
                rfl

theorem cell22_175858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 11].length) (baseStart_175858 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_175858 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_175858 prefixEnd_175858 := by exact prefixLift 175858
  have htrace : WordTrace (prefixWord ++ tailWord_175858) baseStart_175858 baseEnd_175858 := by
    simpa [prefixWord, tailWord_175858, baseEnd_175858] using wordTrace_append hprefix tailTrace_175858
  have hstable : (prefixWord ++ tailWord_175858).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175858).length < 2 ^ (prefixWord ++ tailWord_175858).sum := by decide
  have hdescent : baseEnd_175858 < baseStart_175858 := by decide
  rcases family_descends (prefixWord ++ tailWord_175858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175862 : List Nat := [5, 1, 1, 1, 1, 4, 1, 1, 4, 3]
def baseStart_175862 : Nat := 118140960795 + 175862 * 2 ^ 59
def prefixEnd_175862 : Nat := 4983230072969 + 3 ^ 40 * 175862 * 2
def baseEnd_175862 : Nat := 60201156574064115210821

theorem tailTrace_175862 : CollatzResearch.WordTrace tailWord_175862 prefixEnd_175862 60201156574064115210821 := by
  unfold tailWord_175862
  simp only [CollatzResearch.WordTrace]
  refine ⟨400888380555592730219615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4276142725926322455675893 400888380555592730219615)
  ·
    refine ⟨601332570833389095329423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 400888380555592730219615 601332570833389095329423)
    ·
      refine ⟨901998856250083642994135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 601332570833389095329423 901998856250083642994135)
      ·
        refine ⟨1352998284375125464491203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 901998856250083642994135 1352998284375125464491203)
        ·
          refine ⟨2029497426562688196736805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1352998284375125464491203 2029497426562688196736805)
          ·
            refine ⟨380530767480504036888151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2029497426562688196736805 380530767480504036888151)
            ·
              refine ⟨570796151220756055332227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 380530767480504036888151 570796151220756055332227)
              ·
                refine ⟨856194226831134082998341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 570796151220756055332227 856194226831134082998341)
                ·
                  refine ⟨160536417530837640562189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 856194226831134082998341 160536417530837640562189)
                  ·
                    refine ⟨60201156574064115210821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 160536417530837640562189 60201156574064115210821)
                    ·
                      rfl

theorem cell22_175862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 1, 1, 4, 3].length) (baseStart_175862 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_175862 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_175862 prefixEnd_175862 := by exact prefixLift 175862
  have htrace : WordTrace (prefixWord ++ tailWord_175862) baseStart_175862 baseEnd_175862 := by
    simpa [prefixWord, tailWord_175862, baseEnd_175862] using wordTrace_append hprefix tailTrace_175862
  have hstable : (prefixWord ++ tailWord_175862).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175862).length < 2 ^ (prefixWord ++ tailWord_175862).sum := by decide
  have hdescent : baseEnd_175862 < baseStart_175862 := by decide
  rcases family_descends (prefixWord ++ tailWord_175862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175879 : List Nat := [1, 1, 4, 4, 3, 1, 1, 1, 1, 5]
def baseStart_175879 : Nat := 118140960795 + 175879 * 2 ^ 59
def prefixEnd_175879 : Nat := 4983230072969 + 3 ^ 40 * 175879 * 2
def baseEnd_175879 : Nat := 60206976021481737535769

theorem tailTrace_175879 : CollatzResearch.WordTrace tailWord_175879 prefixEnd_175879 60206976021481737535769 := by
  unfold tailWord_175879
  simp only [CollatzResearch.WordTrace]
  refine ⟨6414834129827895586882691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4276556086551930391255127 6414834129827895586882691)
  ·
    refine ⟨9622251194741843380324037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6414834129827895586882691 9622251194741843380324037)
    ·
      refine ⟨1804172099014095633810757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9622251194741843380324037 1804172099014095633810757)
      ·
        refine ⟨338282268565142931339517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1804172099014095633810757 338282268565142931339517)
        ·
          refine ⟨126855850711928599252319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 338282268565142931339517 126855850711928599252319)
          ·
            refine ⟨190283776067892898878479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126855850711928599252319 190283776067892898878479)
            ·
              refine ⟨285425664101839348317719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 190283776067892898878479 285425664101839348317719)
              ·
                refine ⟨428138496152759022476579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 285425664101839348317719 428138496152759022476579)
                ·
                  refine ⟨642207744229138533714869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 428138496152759022476579 642207744229138533714869)
                  ·
                    refine ⟨60206976021481737535769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 642207744229138533714869 60206976021481737535769)
                    ·
                      rfl

theorem cell22_175879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 1, 1, 1, 5].length) (baseStart_175879 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_175879 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_175879 prefixEnd_175879 := by exact prefixLift 175879
  have htrace : WordTrace (prefixWord ++ tailWord_175879) baseStart_175879 baseEnd_175879 := by
    simpa [prefixWord, tailWord_175879, baseEnd_175879] using wordTrace_append hprefix tailTrace_175879
  have hstable : (prefixWord ++ tailWord_175879).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175879).length < 2 ^ (prefixWord ++ tailWord_175879).sum := by decide
  have hdescent : baseEnd_175879 < baseStart_175879 := by decide
  rcases family_descends (prefixWord ++ tailWord_175879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175903 : List Nat := [1, 1, 2, 4, 2, 1, 1, 1, 9]
def baseStart_175903 : Nat := 118140960795 + 175903 * 2 ^ 59
def prefixEnd_175903 : Nat := 4983230072969 + 3 ^ 40 * 175903 * 2
def baseEnd_175903 : Nat := 20071730570651224978565

theorem tailTrace_175903 : CollatzResearch.WordTrace tailWord_175903 prefixEnd_175903 20071730570651224978565 := by
  unfold tailWord_175903
  simp only [CollatzResearch.WordTrace]
  refine ⟨6415709481740947685756363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4277139654493965123837575 6415709481740947685756363)
  ·
    refine ⟨9623564222611421528634545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6415709481740947685756363 9623564222611421528634545)
    ·
      refine ⟨7217673166958566146475909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9623564222611421528634545 7217673166958566146475909)
      ·
        refine ⟨1353313718804731152464233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7217673166958566146475909 1353313718804731152464233)
        ·
          refine ⟨1014985289103548364348175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1353313718804731152464233 1014985289103548364348175)
          ·
            refine ⟨1522477933655322546522263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1014985289103548364348175 1522477933655322546522263)
            ·
              refine ⟨2283716900482983819783395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1522477933655322546522263 2283716900482983819783395)
              ·
                refine ⟨3425575350724475729675093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2283716900482983819783395 3425575350724475729675093)
                ·
                  refine ⟨20071730570651224978565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 3425575350724475729675093 20071730570651224978565)
                  ·
                    rfl

theorem cell22_175903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 1, 9].length) (baseStart_175903 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_175903 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_175903 prefixEnd_175903 := by exact prefixLift 175903
  have htrace : WordTrace (prefixWord ++ tailWord_175903) baseStart_175903 baseEnd_175903 := by
    simpa [prefixWord, tailWord_175903, baseEnd_175903] using wordTrace_append hprefix tailTrace_175903
  have hstable : (prefixWord ++ tailWord_175903).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175903).length < 2 ^ (prefixWord ++ tailWord_175903).sum := by decide
  have hdescent : baseEnd_175903 < baseStart_175903 := by decide
  rcases family_descends (prefixWord ++ tailWord_175903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175924 : List Nat := [2, 5, 1, 1, 2, 1, 3, 1, 3, 3]
def baseStart_175924 : Nat := 118140960795 + 175924 * 2 ^ 59
def prefixEnd_175924 : Nat := 4983230072969 + 3 ^ 40 * 175924 * 2
def baseEnd_175924 : Nat := 60222380441116620160631

theorem tailTrace_175924 : CollatzResearch.WordTrace tailWord_175924 prefixEnd_175924 60222380441116620160631 := by
  unfold tailWord_175924
  simp only [CollatzResearch.WordTrace]
  refine ⟨3208237707332434136135413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4277650276443245514847217 3208237707332434136135413)
  ·
    refine ⟨300772285062415700262695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3208237707332434136135413 300772285062415700262695)
    ·
      refine ⟨451158427593623550394043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 300772285062415700262695 451158427593623550394043)
      ·
        refine ⟨676737641390435325591065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 451158427593623550394043 676737641390435325591065)
        ·
          refine ⟨507553231042826494193299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 676737641390435325591065 507553231042826494193299)
          ·
            refine ⟨761329846564239741289949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 507553231042826494193299 761329846564239741289949)
            ·
              refine ⟨285498692461589902983731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 761329846564239741289949 285498692461589902983731)
              ·
                refine ⟨428248038692384854475597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 285498692461589902983731 428248038692384854475597)
                ·
                  refine ⟨160593014509644320428349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 428248038692384854475597 160593014509644320428349)
                  ·
                    refine ⟨60222380441116620160631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 160593014509644320428349 60222380441116620160631)
                    ·
                      rfl

theorem cell22_175924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 3, 1, 3, 3].length) (baseStart_175924 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_175924 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_175924 prefixEnd_175924 := by exact prefixLift 175924
  have htrace : WordTrace (prefixWord ++ tailWord_175924) baseStart_175924 baseEnd_175924 := by
    simpa [prefixWord, tailWord_175924, baseEnd_175924] using wordTrace_append hprefix tailTrace_175924
  have hstable : (prefixWord ++ tailWord_175924).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175924).length < 2 ^ (prefixWord ++ tailWord_175924).sum := by decide
  have hdescent : baseEnd_175924 < baseStart_175924 := by decide
  rcases family_descends (prefixWord ++ tailWord_175924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176031 : List Nat := [1, 1, 2, 5, 3, 2, 1, 2, 2, 3]
def baseStart_176031 : Nat := 118140960795 + 176031 * 2 ^ 59
def prefixEnd_176031 : Nat := 4983230072969 + 3 ^ 40 * 176031 * 2
def baseEnd_176031 : Nat := 60259008727804007735303

theorem tailTrace_176031 : CollatzResearch.WordTrace tailWord_176031 prefixEnd_176031 60259008727804007735303 := by
  unfold tailWord_176031
  simp only [CollatzResearch.WordTrace]
  refine ⟨6420378025277225546415947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4280252016851483697610631 6420378025277225546415947)
  ·
    refine ⟨9630567037915838319623921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6420378025277225546415947 9630567037915838319623921)
    ·
      refine ⟨7222925278436878739717941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9630567037915838319623921 7222925278436878739717941)
      ·
        refine ⟨677149244853457381848557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7222925278436878739717941 677149244853457381848557)
        ·
          refine ⟨253930966820046518193209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 677149244853457381848557 253930966820046518193209)
          ·
            refine ⟨190448225115034888644907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 253930966820046518193209 190448225115034888644907)
            ·
              refine ⟨285672337672552332967361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 190448225115034888644907 285672337672552332967361)
              ·
                refine ⟨214254253254414249725521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 285672337672552332967361 214254253254414249725521)
                ·
                  refine ⟨160690689940810687294141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 214254253254414249725521 160690689940810687294141)
                  ·
                    refine ⟨60259008727804007735303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 160690689940810687294141 60259008727804007735303)
                    ·
                      rfl

theorem cell22_176031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 1, 2, 2, 3].length) (baseStart_176031 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_176031 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_176031 prefixEnd_176031 := by exact prefixLift 176031
  have htrace : WordTrace (prefixWord ++ tailWord_176031) baseStart_176031 baseEnd_176031 := by
    simpa [prefixWord, tailWord_176031, baseEnd_176031] using wordTrace_append hprefix tailTrace_176031
  have hstable : (prefixWord ++ tailWord_176031).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176031).length < 2 ^ (prefixWord ++ tailWord_176031).sum := by decide
  have hdescent : baseEnd_176031 < baseStart_176031 := by decide
  rcases family_descends (prefixWord ++ tailWord_176031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176076 : List Nat := [2, 2, 1, 4, 1, 2, 3, 3, 1, 3]
def baseStart_176076 : Nat := 118140960795 + 176076 * 2 ^ 59
def prefixEnd_176076 : Nat := 4983230072969 + 3 ^ 40 * 176076 * 2
def baseEnd_176076 : Nat := 60274413147438890360165

theorem tailTrace_176076 : CollatzResearch.WordTrace tailWord_176076 prefixEnd_176076 60274413147438890360165 := by
  unfold tailWord_176076
  simp only [CollatzResearch.WordTrace]
  refine ⟨3211009655057099115902041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4281346206742798821202721 3211009655057099115902041)
  ·
    refine ⟨2408257241292824336926531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3211009655057099115902041 2408257241292824336926531)
    ·
      refine ⟨3612385861939236505389797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2408257241292824336926531 3612385861939236505389797)
      ·
        refine ⟨677322349113606844760587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3612385861939236505389797 677322349113606844760587)
        ·
          refine ⟨1015983523670410267140881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 677322349113606844760587 1015983523670410267140881)
          ·
            refine ⟨761987642752807700355661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1015983523670410267140881 761987642752807700355661)
            ·
              refine ⟨285745366032302887633373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 761987642752807700355661 285745366032302887633373)
              ·
                refine ⟨107154512262113582862515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 285745366032302887633373 107154512262113582862515)
                ·
                  refine ⟨160731768393170374293773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 107154512262113582862515 160731768393170374293773)
                  ·
                    refine ⟨60274413147438890360165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 160731768393170374293773 60274413147438890360165)
                    ·
                      rfl

theorem cell22_176076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 3, 3, 1, 3].length) (baseStart_176076 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_176076 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_176076 prefixEnd_176076 := by exact prefixLift 176076
  have htrace : WordTrace (prefixWord ++ tailWord_176076) baseStart_176076 baseEnd_176076 := by
    simpa [prefixWord, tailWord_176076, baseEnd_176076] using wordTrace_append hprefix tailTrace_176076
  have hstable : (prefixWord ++ tailWord_176076).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176076).length < 2 ^ (prefixWord ++ tailWord_176076).sum := by decide
  have hdescent : baseEnd_176076 < baseStart_176076 := by decide
  rcases family_descends (prefixWord ++ tailWord_176076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176093 : List Nat := [1, 4, 3, 1, 4, 1, 1, 1, 3, 3]
def baseStart_176093 : Nat := 118140960795 + 176093 * 2 ^ 59
def prefixEnd_176093 : Nat := 4983230072969 + 3 ^ 40 * 176093 * 2
def baseEnd_176093 : Nat := 60280232594856512685113

theorem tailTrace_176093 : CollatzResearch.WordTrace tailWord_176093 prefixEnd_176093 60280232594856512685113 := by
  unfold tailWord_176093
  simp only [CollatzResearch.WordTrace]
  refine ⟨6422639351052610135172933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4281759567368406756781955 6422639351052610135172933)
  ·
    refine ⟨1204244878322364400344925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6422639351052610135172933 1204244878322364400344925)
    ·
      refine ⟨451591829370886650129347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1204244878322364400344925 451591829370886650129347)
      ·
        refine ⟨677387744056329975194021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 451591829370886650129347 677387744056329975194021)
        ·
          refine ⟨127010202010561870348879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 677387744056329975194021 127010202010561870348879)
          ·
            refine ⟨190515303015842805523319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127010202010561870348879 190515303015842805523319)
            ·
              refine ⟨285772954523764208284979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 190515303015842805523319 285772954523764208284979)
              ·
                refine ⟨428659431785646312427469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 285772954523764208284979 428659431785646312427469)
                ·
                  refine ⟨160747286919617367160301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 428659431785646312427469 160747286919617367160301)
                  ·
                    refine ⟨60280232594856512685113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 160747286919617367160301 60280232594856512685113)
                    ·
                      rfl

theorem cell22_176093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 1, 1, 3, 3].length) (baseStart_176093 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_176093 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_176093 prefixEnd_176093 := by exact prefixLift 176093
  have htrace : WordTrace (prefixWord ++ tailWord_176093) baseStart_176093 baseEnd_176093 := by
    simpa [prefixWord, tailWord_176093, baseEnd_176093] using wordTrace_append hprefix tailTrace_176093
  have hstable : (prefixWord ++ tailWord_176093).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176093).length < 2 ^ (prefixWord ++ tailWord_176093).sum := by decide
  have hdescent : baseEnd_176093 < baseStart_176093 := by decide
  rcases family_descends (prefixWord ++ tailWord_176093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176115 : List Nat := [1, 1, 1, 2, 2, 2, 1, 2, 5, 5]
def baseStart_176115 : Nat := 118140960795 + 176115 * 2 ^ 59
def prefixEnd_176115 : Nat := 4983230072969 + 3 ^ 40 * 176115 * 2
def baseEnd_176115 : Nat := 60287763644455788635045

theorem tailTrace_176115 : CollatzResearch.WordTrace tailWord_176115 prefixEnd_176115 60287763644455788635045 := by
  unfold tailWord_176115
  simp only [CollatzResearch.WordTrace]
  refine ⟨6423441756972907892473799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4282294504648605261649199 6423441756972907892473799)
  ·
    refine ⟨9635162635459361838710699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6423441756972907892473799 9635162635459361838710699)
    ·
      refine ⟨14452743953189042758066049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9635162635459361838710699 14452743953189042758066049)
      ·
        refine ⟨10839557964891782068549537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14452743953189042758066049 10839557964891782068549537)
        ·
          refine ⟨8129668473668836551412153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10839557964891782068549537 8129668473668836551412153)
          ·
            refine ⟨6097251355251627413559115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8129668473668836551412153 6097251355251627413559115)
            ·
              refine ⟨9145877032877441120338673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6097251355251627413559115 9145877032877441120338673)
              ·
                refine ⟨6859407774658080840254005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9145877032877441120338673 6859407774658080840254005)
                ·
                  refine ⟨643069478874195078773813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 6859407774658080840254005 643069478874195078773813)
                  ·
                    refine ⟨60287763644455788635045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 643069478874195078773813 60287763644455788635045)
                    ·
                      rfl

theorem cell22_176115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 2, 5, 5].length) (baseStart_176115 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_176115 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_176115 prefixEnd_176115 := by exact prefixLift 176115
  have htrace : WordTrace (prefixWord ++ tailWord_176115) baseStart_176115 baseEnd_176115 := by
    simpa [prefixWord, tailWord_176115, baseEnd_176115] using wordTrace_append hprefix tailTrace_176115
  have hstable : (prefixWord ++ tailWord_176115).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176115).length < 2 ^ (prefixWord ++ tailWord_176115).sum := by decide
  have hdescent : baseEnd_176115 < baseStart_176115 := by decide
  rcases family_descends (prefixWord ++ tailWord_176115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176147 : List Nat := [1, 1, 1, 2, 1, 4, 4, 2, 2, 4]
def baseStart_176147 : Nat := 118140960795 + 176147 * 2 ^ 59
def prefixEnd_176147 : Nat := 4983230072969 + 3 ^ 40 * 176147 * 2
def baseEnd_176147 : Nat := 60298717898418371834947

theorem tailTrace_176147 : CollatzResearch.WordTrace tailWord_176147 prefixEnd_176147 60298717898418371834947 := by
  unfold tailWord_176147
  simp only [CollatzResearch.WordTrace]
  refine ⟨6424608892856977357638695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4283072595237984905092463 6424608892856977357638695)
  ·
    refine ⟨9636913339285466036458043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6424608892856977357638695 9636913339285466036458043)
    ·
      refine ⟨14455370008928199054687065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9636913339285466036458043 14455370008928199054687065)
      ·
        refine ⟨10841527506696149291015299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14455370008928199054687065 10841527506696149291015299)
        ·
          refine ⟨16262291260044223936522949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10841527506696149291015299 16262291260044223936522949)
          ·
            refine ⟨3049179611258291988098053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16262291260044223936522949 3049179611258291988098053)
            ·
              refine ⟨571721177110929747768385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3049179611258291988098053 571721177110929747768385)
              ·
                refine ⟨428790882833197310826289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 571721177110929747768385 428790882833197310826289)
                ·
                  refine ⟨321593162124897983119717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 428790882833197310826289 321593162124897983119717)
                  ·
                    refine ⟨60298717898418371834947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 321593162124897983119717 60298717898418371834947)
                    ·
                      rfl

theorem cell22_176147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 4, 2, 2, 4].length) (baseStart_176147 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_176147 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_176147 prefixEnd_176147 := by exact prefixLift 176147
  have htrace : WordTrace (prefixWord ++ tailWord_176147) baseStart_176147 baseEnd_176147 := by
    simpa [prefixWord, tailWord_176147, baseEnd_176147] using wordTrace_append hprefix tailTrace_176147
  have hstable : (prefixWord ++ tailWord_176147).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176147).length < 2 ^ (prefixWord ++ tailWord_176147).sum := by decide
  have hdescent : baseEnd_176147 < baseStart_176147 := by decide
  rcases family_descends (prefixWord ++ tailWord_176147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176151 : List Nat := [1, 1, 3, 5, 2, 1, 1, 4, 4]
def baseStart_176151 : Nat := 118140960795 + 176151 * 2 ^ 59
def prefixEnd_176151 : Nat := 4983230072969 + 3 ^ 40 * 176151 * 2
def baseEnd_176151 : Nat := 20100029060054564911645

theorem tailTrace_176151 : CollatzResearch.WordTrace tailWord_176151 prefixEnd_176151 20100029060054564911645 := by
  unfold tailWord_176151
  simp only [CollatzResearch.WordTrace]
  refine ⟨6424754784842486040784307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4283169856561657360522871 6424754784842486040784307)
  ·
    refine ⟨9637132177263729061176461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6424754784842486040784307 9637132177263729061176461)
    ·
      refine ⟨3613924566473898397941173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9637132177263729061176461 3613924566473898397941173)
      ·
        refine ⟨338805428106927974806985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3613924566473898397941173 338805428106927974806985)
        ·
          refine ⟨254104071080195981105239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 338805428106927974806985 254104071080195981105239)
          ·
            refine ⟨381156106620293971657859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 254104071080195981105239 381156106620293971657859)
            ·
              refine ⟨571734159930440957486789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 381156106620293971657859 571734159930440957486789)
              ·
                refine ⟨107200154986957679528773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 571734159930440957486789 107200154986957679528773)
                ·
                  refine ⟨20100029060054564911645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 107200154986957679528773 20100029060054564911645)
                  ·
                    rfl

theorem cell22_176151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 1, 4, 4].length) (baseStart_176151 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_176151 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_176151 prefixEnd_176151 := by exact prefixLift 176151
  have htrace : WordTrace (prefixWord ++ tailWord_176151) baseStart_176151 baseEnd_176151 := by
    simpa [prefixWord, tailWord_176151, baseEnd_176151] using wordTrace_append hprefix tailTrace_176151
  have hstable : (prefixWord ++ tailWord_176151).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176151).length < 2 ^ (prefixWord ++ tailWord_176151).sum := by decide
  have hdescent : baseEnd_176151 < baseStart_176151 := by decide
  rcases family_descends (prefixWord ++ tailWord_176151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176284 : List Nat := [2, 2, 3, 2, 1, 1, 2, 3, 1, 5]
def baseStart_176284 : Nat := 118140960795 + 176284 * 2 ^ 59
def prefixEnd_176284 : Nat := 4983230072969 + 3 ^ 40 * 176284 * 2
def baseEnd_176284 : Nat := 60345615798195681159527

theorem tailTrace_176284 : CollatzResearch.WordTrace tailWord_176284 prefixEnd_176284 60345615798195681159527 := by
  unfold tailWord_176284
  simp only [CollatzResearch.WordTrace]
  refine ⟨3214802846680324877687953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4286403795573766503583937 3214802846680324877687953)
  ·
    refine ⟨2411102135010243658265965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3214802846680324877687953 2411102135010243658265965)
    ·
      refine ⟨904163300628841371849737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2411102135010243658265965 904163300628841371849737)
      ·
        refine ⟨678122475471631028887303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 904163300628841371849737 678122475471631028887303)
        ·
          refine ⟨1017183713207446543330955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 678122475471631028887303 1017183713207446543330955)
          ·
            refine ⟨1525775569811169814996433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1017183713207446543330955 1525775569811169814996433)
            ·
              refine ⟨1144331677358377361247325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1525775569811169814996433 1144331677358377361247325)
              ·
                refine ⟨429124379009391510467747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1144331677358377361247325 429124379009391510467747)
                ·
                  refine ⟨643686568514087265701621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 429124379009391510467747 643686568514087265701621)
                  ·
                    refine ⟨60345615798195681159527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 643686568514087265701621 60345615798195681159527)
                    ·
                      rfl

theorem cell22_176284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 3, 1, 5].length) (baseStart_176284 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_176284 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_176284 prefixEnd_176284 := by exact prefixLift 176284
  have htrace : WordTrace (prefixWord ++ tailWord_176284) baseStart_176284 baseEnd_176284 := by
    simpa [prefixWord, tailWord_176284, baseEnd_176284] using wordTrace_append hprefix tailTrace_176284
  have hstable : (prefixWord ++ tailWord_176284).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176284).length < 2 ^ (prefixWord ++ tailWord_176284).sum := by decide
  have hdescent : baseEnd_176284 < baseStart_176284 := by decide
  rcases family_descends (prefixWord ++ tailWord_176284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176301 : List Nat := [1, 5, 2, 1, 2, 2, 1, 2, 1, 5]
def baseStart_176301 : Nat := 118140960795 + 176301 * 2 ^ 59
def prefixEnd_176301 : Nat := 4983230072969 + 3 ^ 40 * 176301 * 2
def baseEnd_176301 : Nat := 60351435245613303484475

theorem tailTrace_176301 : CollatzResearch.WordTrace tailWord_176301 prefixEnd_176301 60351435245613303484475 := by
  unfold tailWord_176301
  simp only [CollatzResearch.WordTrace]
  refine ⟨6430225734299061658744757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4286817156199374439163171 6430225734299061658744757)
  ·
    refine ⟨602833662590537030507321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6430225734299061658744757 602833662590537030507321)
    ·
      refine ⟨452125246942902772880491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 602833662590537030507321 452125246942902772880491)
      ·
        refine ⟨678187870414354159320737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 452125246942902772880491 678187870414354159320737)
        ·
          refine ⟨508640902810765619490553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 678187870414354159320737 508640902810765619490553)
          ·
            refine ⟨381480677108074214617915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 508640902810765619490553 381480677108074214617915)
            ·
              refine ⟨572221015662111321926873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 381480677108074214617915 572221015662111321926873)
              ·
                refine ⟨429165761746583491445155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 572221015662111321926873 429165761746583491445155)
                ·
                  refine ⟨643748642619875237167733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 429165761746583491445155 643748642619875237167733)
                  ·
                    refine ⟨60351435245613303484475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 643748642619875237167733 60351435245613303484475)
                    ·
                      rfl

theorem cell22_176301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 1, 2, 1, 5].length) (baseStart_176301 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_176301 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_176301 prefixEnd_176301 := by exact prefixLift 176301
  have htrace : WordTrace (prefixWord ++ tailWord_176301) baseStart_176301 baseEnd_176301 := by
    simpa [prefixWord, tailWord_176301, baseEnd_176301] using wordTrace_append hprefix tailTrace_176301
  have hstable : (prefixWord ++ tailWord_176301).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176301).length < 2 ^ (prefixWord ++ tailWord_176301).sum := by decide
  have hdescent : baseEnd_176301 < baseStart_176301 := by decide
  rcases family_descends (prefixWord ++ tailWord_176301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176363 : List Nat := [1, 1, 1, 1, 2, 5, 4, 3, 1, 3]
def baseStart_176363 : Nat := 118140960795 + 176363 * 2 ^ 59
def prefixEnd_176363 : Nat := 4983230072969 + 3 ^ 40 * 176363 * 2
def baseEnd_176363 : Nat := 60372659112665808434285

theorem tailTrace_176363 : CollatzResearch.WordTrace tailWord_176363 prefixEnd_176363 60372659112665808434285 := by
  unfold tailWord_176363
  simp only [CollatzResearch.WordTrace]
  refine ⟨6432487060074446247501743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4288324706716297498334495 6432487060074446247501743)
  ·
    refine ⟨9648730590111669371252615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6432487060074446247501743 9648730590111669371252615)
    ·
      refine ⟨14473095885167504056878923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9648730590111669371252615 14473095885167504056878923)
      ·
        refine ⟨21709643827751256085318385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14473095885167504056878923 21709643827751256085318385)
        ·
          refine ⟨16282232870813442063988789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21709643827751256085318385 16282232870813442063988789)
          ·
            refine ⟨1526459331638760193498949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16282232870813442063988789 1526459331638760193498949)
            ·
              refine ⟨286211124682267536281053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1526459331638760193498949 286211124682267536281053)
              ·
                refine ⟨107329171755850326105395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 286211124682267536281053 107329171755850326105395)
                ·
                  refine ⟨160993757633775489158093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 107329171755850326105395 160993757633775489158093)
                  ·
                    refine ⟨60372659112665808434285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 160993757633775489158093 60372659112665808434285)
                    ·
                      rfl

theorem cell22_176363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 4, 3, 1, 3].length) (baseStart_176363 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_176363 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_176363 prefixEnd_176363 := by exact prefixLift 176363
  have htrace : WordTrace (prefixWord ++ tailWord_176363) baseStart_176363 baseEnd_176363 := by
    simpa [prefixWord, tailWord_176363, baseEnd_176363] using wordTrace_append hprefix tailTrace_176363
  have hstable : (prefixWord ++ tailWord_176363).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176363).length < 2 ^ (prefixWord ++ tailWord_176363).sum := by decide
  have hdescent : baseEnd_176363 < baseStart_176363 := by decide
  rcases family_descends (prefixWord ++ tailWord_176363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176389 : List Nat := [1, 3, 1, 1, 2, 1, 2, 4, 3, 4]
def baseStart_176389 : Nat := 118140960795 + 176389 * 2 ^ 59
def prefixEnd_176389 : Nat := 4983230072969 + 3 ^ 40 * 176389 * 2
def baseEnd_176389 : Nat := 60381559444010407284205

theorem tailTrace_176389 : CollatzResearch.WordTrace tailWord_176389 prefixEnd_176389 60381559444010407284205 := by
  unfold tailWord_176389
  simp only [CollatzResearch.WordTrace]
  refine ⟨6433435357980252687948221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4288956905320168458632147 6433435357980252687948221)
  ·
    refine ⟨2412538259242594757980583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6433435357980252687948221 2412538259242594757980583)
    ·
      refine ⟨3618807388863892136970875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2412538259242594757980583 3618807388863892136970875)
      ·
        refine ⟨5428211083295838205456313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3618807388863892136970875 5428211083295838205456313)
        ·
          refine ⟨4071158312471878654092235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5428211083295838205456313 4071158312471878654092235)
          ·
            refine ⟨6106737468707817981138353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4071158312471878654092235 6106737468707817981138353)
            ·
              refine ⟨4580053101530863485853765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6106737468707817981138353 4580053101530863485853765)
              ·
                refine ⟨858759956537036903597581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4580053101530863485853765 858759956537036903597581)
                ·
                  refine ⟨322034983701388838849093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 858759956537036903597581 322034983701388838849093)
                  ·
                    refine ⟨60381559444010407284205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 322034983701388838849093 60381559444010407284205)
                    ·
                      rfl

theorem cell22_176389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 4, 3, 4].length) (baseStart_176389 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_176389 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_176389 prefixEnd_176389 := by exact prefixLift 176389
  have htrace : WordTrace (prefixWord ++ tailWord_176389) baseStart_176389 baseEnd_176389 := by
    simpa [prefixWord, tailWord_176389, baseEnd_176389] using wordTrace_append hprefix tailTrace_176389
  have hstable : (prefixWord ++ tailWord_176389).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176389).length < 2 ^ (prefixWord ++ tailWord_176389).sum := by decide
  have hdescent : baseEnd_176389 < baseStart_176389 := by decide
  rcases family_descends (prefixWord ++ tailWord_176389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176414 : List Nat := [4, 3, 2, 1, 1, 3, 1, 3, 1, 3]
def baseStart_176414 : Nat := 118140960795 + 176414 * 2 ^ 59
def prefixEnd_176414 : Nat := 4983230072969 + 3 ^ 40 * 176414 * 2
def baseEnd_176414 : Nat := 60390117454918675409129

theorem tailTrace_176414 : CollatzResearch.WordTrace tailWord_176414 prefixEnd_176414 60390117454918675409129 := by
  unfold tailWord_176414
  simp only [CollatzResearch.WordTrace]
  refine ⟨804293397861210244701037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4289564788593121305072197 804293397861210244701037)
  ·
    refine ⟨301610024197953841762889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 804293397861210244701037 301610024197953841762889)
    ·
      refine ⟨226207518148465381322167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 301610024197953841762889 226207518148465381322167)
      ·
        refine ⟨339311277222698071983251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 226207518148465381322167 339311277222698071983251)
        ·
          refine ⟨508966915834047107974877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 339311277222698071983251 508966915834047107974877)
          ·
            refine ⟨190862593437767665490579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 508966915834047107974877 190862593437767665490579)
            ·
              refine ⟨286293890156651498235869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 190862593437767665490579 286293890156651498235869)
              ·
                refine ⟨107360208808744311838451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 286293890156651498235869 107360208808744311838451)
                ·
                  refine ⟨161040313213116467757677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 107360208808744311838451 161040313213116467757677)
                  ·
                    refine ⟨60390117454918675409129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 161040313213116467757677 60390117454918675409129)
                    ·
                      rfl

theorem cell22_176414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 1, 3, 1, 3].length) (baseStart_176414 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_176414 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_176414 prefixEnd_176414 := by exact prefixLift 176414
  have htrace : WordTrace (prefixWord ++ tailWord_176414) baseStart_176414 baseEnd_176414 := by
    simpa [prefixWord, tailWord_176414, baseEnd_176414] using wordTrace_append hprefix tailTrace_176414
  have hstable : (prefixWord ++ tailWord_176414).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176414).length < 2 ^ (prefixWord ++ tailWord_176414).sum := by decide
  have hdescent : baseEnd_176414 < baseStart_176414 := by decide
  rcases family_descends (prefixWord ++ tailWord_176414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176419 : List Nat := [1, 1, 1, 4, 2, 2, 2, 1, 3, 5]
def baseStart_176419 : Nat := 118140960795 + 176419 * 2 ^ 59
def prefixEnd_176419 : Nat := 4983230072969 + 3 ^ 40 * 176419 * 2
def baseEnd_176419 : Nat := 60391829057100329034113

theorem tailTrace_176419 : CollatzResearch.WordTrace tailWord_176419 prefixEnd_176419 60391829057100329034113 := by
  unfold tailWord_176419
  simp only [CollatzResearch.WordTrace]
  refine ⟨6434529547871567811540311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4289686365247711874360207 6434529547871567811540311)
  ·
    refine ⟨9651794321807351717310467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6434529547871567811540311 9651794321807351717310467)
    ·
      refine ⟨14477691482711027575965701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9651794321807351717310467 14477691482711027575965701)
      ·
        refine ⟨2714567153008317670493569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14477691482711027575965701 2714567153008317670493569)
        ·
          refine ⟨2035925364756238252870177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2714567153008317670493569 2035925364756238252870177)
          ·
            refine ⟨1526944023567178689652633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2035925364756238252870177 1526944023567178689652633)
            ·
              refine ⟨1145208017675384017239475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1526944023567178689652633 1145208017675384017239475)
              ·
                refine ⟨1717812026513076025859213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1145208017675384017239475 1717812026513076025859213)
                ·
                  refine ⟨644179509942403509697205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1717812026513076025859213 644179509942403509697205)
                  ·
                    refine ⟨60391829057100329034113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 644179509942403509697205 60391829057100329034113)
                    ·
                      rfl

theorem cell22_176419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 1, 3, 5].length) (baseStart_176419 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_176419 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_176419 prefixEnd_176419 := by exact prefixLift 176419
  have htrace : WordTrace (prefixWord ++ tailWord_176419) baseStart_176419 baseEnd_176419 := by
    simpa [prefixWord, tailWord_176419, baseEnd_176419] using wordTrace_append hprefix tailTrace_176419
  have hstable : (prefixWord ++ tailWord_176419).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176419).length < 2 ^ (prefixWord ++ tailWord_176419).sum := by decide
  have hdescent : baseEnd_176419 < baseStart_176419 := by decide
  rcases family_descends (prefixWord ++ tailWord_176419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176468 : List Nat := [2, 4, 1, 1, 2, 3, 2, 1, 2, 4]
def baseStart_176468 : Nat := 118140960795 + 176468 * 2 ^ 59
def prefixEnd_176468 : Nat := 4983230072969 + 3 ^ 40 * 176468 * 2
def baseEnd_176468 : Nat := 60408602758480534558963

theorem tailTrace_176468 : CollatzResearch.WordTrace tailWord_176468 prefixEnd_176468 60408602758480534558963 := by
  unfold tailWord_176468
  simp only [CollatzResearch.WordTrace]
  refine ⟨3218158362347024590037029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4290877816462699453382705 3218158362347024590037029)
  ·
    refine ⟨603404692940067110631943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3218158362347024590037029 603404692940067110631943)
    ·
      refine ⟨905107039410100665947915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 603404692940067110631943 905107039410100665947915)
      ·
        refine ⟨1357660559115150998921873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 905107039410100665947915 1357660559115150998921873)
        ·
          refine ⟨1018245419336363249191405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1357660559115150998921873 1018245419336363249191405)
          ·
            refine ⟨381842032251136218446777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1018245419336363249191405 381842032251136218446777)
            ·
              refine ⟨286381524188352163835083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 381842032251136218446777 286381524188352163835083)
              ·
                refine ⟨429572286282528245752625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 286381524188352163835083 429572286282528245752625)
                ·
                  refine ⟨322179214711896184314469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 429572286282528245752625 322179214711896184314469)
                  ·
                    refine ⟨60408602758480534558963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 322179214711896184314469 60408602758480534558963)
                    ·
                      rfl

theorem cell22_176468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 2, 1, 2, 4].length) (baseStart_176468 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_176468 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_176468 prefixEnd_176468 := by exact prefixLift 176468
  have htrace : WordTrace (prefixWord ++ tailWord_176468) baseStart_176468 baseEnd_176468 := by
    simpa [prefixWord, tailWord_176468, baseEnd_176468] using wordTrace_append hprefix tailTrace_176468
  have hstable : (prefixWord ++ tailWord_176468).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176468).length < 2 ^ (prefixWord ++ tailWord_176468).sum := by decide
  have hdescent : baseEnd_176468 < baseStart_176468 := by decide
  rcases family_descends (prefixWord ++ tailWord_176468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176586 : List Nat := [3, 1, 2, 1, 2, 2, 1, 3, 1, 6]
def baseStart_176586 : Nat := 118140960795 + 176586 * 2 ^ 59
def prefixEnd_176586 : Nat := 4983230072969 + 3 ^ 40 * 176586 * 2
def baseEnd_176586 : Nat := 60448996569967560108601

theorem tailTrace_176586 : CollatzResearch.WordTrace tailWord_176586 prefixEnd_176586 60448996569967560108601 := by
  unfold tailWord_176586
  simp only [CollatzResearch.WordTrace]
  refine ⟨1610155134566638833217403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4293747025511036888579741 1610155134566638833217403)
  ·
    refine ⟨2415232701849958249826105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1610155134566638833217403 2415232701849958249826105)
    ·
      refine ⟨1811424526387468687369579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2415232701849958249826105 1811424526387468687369579)
      ·
        refine ⟨2717136789581203031054369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1811424526387468687369579 2717136789581203031054369)
        ·
          refine ⟨2037852592185902273290777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2717136789581203031054369 2037852592185902273290777)
          ·
            refine ⟨1528389444139426704968083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2037852592185902273290777 1528389444139426704968083)
            ·
              refine ⟨2292584166209140057452125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1528389444139426704968083 2292584166209140057452125)
              ·
                refine ⟨859719062328427521544547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2292584166209140057452125 859719062328427521544547)
                ·
                  refine ⟨1289578593492641282316821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 859719062328427521544547 1289578593492641282316821)
                  ·
                    refine ⟨60448996569967560108601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1289578593492641282316821 60448996569967560108601)
                    ·
                      rfl

theorem cell22_176586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 3, 1, 6].length) (baseStart_176586 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_176586 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_176586 prefixEnd_176586 := by exact prefixLift 176586
  have htrace : WordTrace (prefixWord ++ tailWord_176586) baseStart_176586 baseEnd_176586 := by
    simpa [prefixWord, tailWord_176586, baseEnd_176586] using wordTrace_append hprefix tailTrace_176586
  have hstable : (prefixWord ++ tailWord_176586).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176586).length < 2 ^ (prefixWord ++ tailWord_176586).sum := by decide
  have hdescent : baseEnd_176586 < baseStart_176586 := by decide
  rcases family_descends (prefixWord ++ tailWord_176586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176605 : List Nat := [1, 4, 3, 1, 1, 1, 2, 4, 2, 3]
def baseStart_176605 : Nat := 118140960795 + 176605 * 2 ^ 59
def prefixEnd_176605 : Nat := 4983230072969 + 3 ^ 40 * 176605 * 2
def baseEnd_176605 : Nat := 60455500658257843883543

theorem tailTrace_176605 : CollatzResearch.WordTrace tailWord_176605 prefixEnd_176605 60455500658257843883543 := by
  unfold tailWord_176605
  simp only [CollatzResearch.WordTrace]
  refine ⟨6441313525197721577811269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4294209016798481051874179 6441313525197721577811269)
  ·
    refine ⟨1207746285974572795839613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6441313525197721577811269 1207746285974572795839613)
    ·
      refine ⟨452904857240464798439855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1207746285974572795839613 452904857240464798439855)
      ·
        refine ⟨679357285860697197659783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 452904857240464798439855 679357285860697197659783)
        ·
          refine ⟨1019035928791045796489675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 679357285860697197659783 1019035928791045796489675)
          ·
            refine ⟨1528553893186568694734513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1019035928791045796489675 1528553893186568694734513)
            ·
              refine ⟨1146415419889926521050885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1528553893186568694734513 1146415419889926521050885)
              ·
                refine ⟨214952891229361222697041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1146415419889926521050885 214952891229361222697041)
                ·
                  refine ⟨161214668422020917022781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 214952891229361222697041 161214668422020917022781)
                  ·
                    refine ⟨60455500658257843883543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 161214668422020917022781 60455500658257843883543)
                    ·
                      rfl

theorem cell22_176605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 4, 2, 3].length) (baseStart_176605 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_176605 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_176605 prefixEnd_176605 := by exact prefixLift 176605
  have htrace : WordTrace (prefixWord ++ tailWord_176605) baseStart_176605 baseEnd_176605 := by
    simpa [prefixWord, tailWord_176605, baseEnd_176605] using wordTrace_append hprefix tailTrace_176605
  have hstable : (prefixWord ++ tailWord_176605).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176605).length < 2 ^ (prefixWord ++ tailWord_176605).sum := by decide
  have hdescent : baseEnd_176605 < baseStart_176605 := by decide
  rcases family_descends (prefixWord ++ tailWord_176605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176618 : List Nat := [3, 1, 3, 1, 3, 2, 2, 7]
def baseStart_176618 : Nat := 118140960795 + 176618 * 2 ^ 59
def prefixEnd_176618 : Nat := 4983230072969 + 3 ^ 40 * 176618 * 2
def baseEnd_176618 : Nat := 6717772313770015923167

theorem tailTrace_176618 : CollatzResearch.WordTrace tailWord_176618 prefixEnd_176618 6717772313770015923167 := by
  unfold tailWord_176618
  simp only [CollatzResearch.WordTrace]
  refine ⟨1610446918537656199508627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4294525116100416532023005 1610446918537656199508627)
  ·
    refine ⟨2415670377806484299262941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1610446918537656199508627 2415670377806484299262941)
    ·
      refine ⟨905876391677431612223603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2415670377806484299262941 905876391677431612223603)
      ·
        refine ⟨1358814587516147418335405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 905876391677431612223603 1358814587516147418335405)
        ·
          refine ⟨509555470318555281875777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1358814587516147418335405 509555470318555281875777)
          ·
            refine ⟨382166602738916461406833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 509555470318555281875777 382166602738916461406833)
            ·
              refine ⟨286624952054187346055125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 382166602738916461406833 286624952054187346055125)
              ·
                refine ⟨6717772313770015923167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 286624952054187346055125 6717772313770015923167)
                ·
                  rfl

theorem cell22_176618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 2, 7].length) (baseStart_176618 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_176618 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_176618 prefixEnd_176618 := by exact prefixLift 176618
  have htrace : WordTrace (prefixWord ++ tailWord_176618) baseStart_176618 baseEnd_176618 := by
    simpa [prefixWord, tailWord_176618, baseEnd_176618] using wordTrace_append hprefix tailTrace_176618
  have hstable : (prefixWord ++ tailWord_176618).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176618).length < 2 ^ (prefixWord ++ tailWord_176618).sum := by decide
  have hdescent : baseEnd_176618 < baseStart_176618 := by decide
  rcases family_descends (prefixWord ++ tailWord_176618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176622 : List Nat := [4, 1, 2, 1, 2, 2, 4, 1, 2, 3]
def baseStart_176622 : Nat := 118140960795 + 176622 * 2 ^ 59
def prefixEnd_176622 : Nat := 4983230072969 + 3 ^ 40 * 176622 * 2
def baseEnd_176622 : Nat := 60461320105675466208491

theorem tailTrace_176622 : CollatzResearch.WordTrace tailWord_176622 prefixEnd_176622 60461320105675466208491 := by
  unfold tailWord_176622
  simp only [CollatzResearch.WordTrace]
  refine ⟨805241695767016685147515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4294622377424088987453413 805241695767016685147515)
  ·
    refine ⟨1207862543650525027721273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 805241695767016685147515 1207862543650525027721273)
    ·
      refine ⟨905896907737893770790955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1207862543650525027721273 905896907737893770790955)
      ·
        refine ⟨1358845361606840656186433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 905896907737893770790955 1358845361606840656186433)
        ·
          refine ⟨1019134021205130492139825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1358845361606840656186433 1019134021205130492139825)
          ·
            refine ⟨764350515903847869104869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1019134021205130492139825 764350515903847869104869)
            ·
              refine ⟨143315721731971475457163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 764350515903847869104869 143315721731971475457163)
              ·
                refine ⟨214973582597957213185745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 143315721731971475457163 214973582597957213185745)
                ·
                  refine ⟨161230186948467909889309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 214973582597957213185745 161230186948467909889309)
                  ·
                    refine ⟨60461320105675466208491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 161230186948467909889309 60461320105675466208491)
                    ·
                      rfl

theorem cell22_176622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 4, 1, 2, 3].length) (baseStart_176622 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_176622 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_176622 prefixEnd_176622 := by exact prefixLift 176622
  have htrace : WordTrace (prefixWord ++ tailWord_176622) baseStart_176622 baseEnd_176622 := by
    simpa [prefixWord, tailWord_176622, baseEnd_176622] using wordTrace_append hprefix tailTrace_176622
  have hstable : (prefixWord ++ tailWord_176622).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176622).length < 2 ^ (prefixWord ++ tailWord_176622).sum := by decide
  have hdescent : baseEnd_176622 < baseStart_176622 := by decide
  rcases family_descends (prefixWord ++ tailWord_176622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176633 : List Nat := [1, 2, 1, 3, 1, 2, 2, 4, 3, 3]
def baseStart_176633 : Nat := 118140960795 + 176633 * 2 ^ 59
def prefixEnd_176633 : Nat := 4983230072969 + 3 ^ 40 * 176633 * 2
def baseEnd_176633 : Nat := 60465085630475104183457

theorem tailTrace_176633 : CollatzResearch.WordTrace tailWord_176633 prefixEnd_176633 60465085630475104183457 := by
  unfold tailWord_176633
  simp only [CollatzResearch.WordTrace]
  refine ⟨6442334769096282359830553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4294889846064188239887035 6442334769096282359830553)
  ·
    refine ⟨4831751076822211769872915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6442334769096282359830553 4831751076822211769872915)
    ·
      refine ⟨7247626615233317654809373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4831751076822211769872915 7247626615233317654809373)
      ·
        refine ⟨2717859980712494120553515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7247626615233317654809373 2717859980712494120553515)
        ·
          refine ⟨4076789971068741180830273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2717859980712494120553515 4076789971068741180830273)
          ·
            refine ⟨3057592478301555885622705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4076789971068741180830273 3057592478301555885622705)
            ·
              refine ⟨2293194358726166914217029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3057592478301555885622705 2293194358726166914217029)
              ·
                refine ⟨429973942261156296415693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2293194358726166914217029 429973942261156296415693)
                ·
                  refine ⟨161240228347933611155885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 429973942261156296415693 161240228347933611155885)
                  ·
                    refine ⟨60465085630475104183457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 161240228347933611155885 60465085630475104183457)
                    ·
                      rfl

theorem cell22_176633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 4, 3, 3].length) (baseStart_176633 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_176633 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_176633 prefixEnd_176633 := by exact prefixLift 176633
  have htrace : WordTrace (prefixWord ++ tailWord_176633) baseStart_176633 baseEnd_176633 := by
    simpa [prefixWord, tailWord_176633, baseEnd_176633] using wordTrace_append hprefix tailTrace_176633
  have hstable : (prefixWord ++ tailWord_176633).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176633).length < 2 ^ (prefixWord ++ tailWord_176633).sum := by decide
  have hdescent : baseEnd_176633 < baseStart_176633 := by decide
  rcases family_descends (prefixWord ++ tailWord_176633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176680 : List Nat := [2, 1, 5, 2, 1, 1, 2, 3, 5]
def baseStart_176680 : Nat := 118140960795 + 176680 * 2 ^ 59
def prefixEnd_176680 : Nat := 4983230072969 + 3 ^ 40 * 176680 * 2
def baseEnd_176680 : Nat := 20160391563660882752771

theorem tailTrace_176680 : CollatzResearch.WordTrace tailWord_176680 prefixEnd_176680 20160391563660882752771 := by
  unfold tailWord_176680
  simp only [CollatzResearch.WordTrace]
  refine ⟨3222024499963004693395747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4296032666617339591194329 3222024499963004693395747)
  ·
    refine ⟨4833036749944507040093621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3222024499963004693395747 4833036749944507040093621)
    ·
      refine ⟨453097195307297535008777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4833036749944507040093621 453097195307297535008777)
      ·
        refine ⟨339822896480473151256583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 453097195307297535008777 339822896480473151256583)
        ·
          refine ⟨509734344720709726884875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 339822896480473151256583 509734344720709726884875)
          ·
            refine ⟨764601517081064590327313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 509734344720709726884875 764601517081064590327313)
            ·
              refine ⟨573451137810798442745485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 764601517081064590327313 573451137810798442745485)
              ·
                refine ⟨215044176679049416029557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 573451137810798442745485 215044176679049416029557)
                ·
                  refine ⟨20160391563660882752771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 215044176679049416029557 20160391563660882752771)
                  ·
                    rfl

theorem cell22_176680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 2, 3, 5].length) (baseStart_176680 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_176680 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_176680 prefixEnd_176680 := by exact prefixLift 176680
  have htrace : WordTrace (prefixWord ++ tailWord_176680) baseStart_176680 baseEnd_176680 := by
    simpa [prefixWord, tailWord_176680, baseEnd_176680] using wordTrace_append hprefix tailTrace_176680
  have hstable : (prefixWord ++ tailWord_176680).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176680).length < 2 ^ (prefixWord ++ tailWord_176680).sum := by decide
  have hdescent : baseEnd_176680 < baseStart_176680 := by decide
  rcases family_descends (prefixWord ++ tailWord_176680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176693 : List Nat := [1, 3, 3, 1, 1, 2, 1, 3, 3, 4]
def baseStart_176693 : Nat := 118140960795 + 176693 * 2 ^ 59
def prefixEnd_176693 : Nat := 4983230072969 + 3 ^ 40 * 176693 * 2
def baseEnd_176693 : Nat := 60485624856654947683273

theorem tailTrace_176693 : CollatzResearch.WordTrace tailWord_176693 prefixEnd_176693 60485624856654947683273 := by
  unfold tailWord_176693
  simp only [CollatzResearch.WordTrace]
  refine ⟨6444523148878912607014733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4296348765919275071343155 6444523148878912607014733)
  ·
    refine ⟨2416696180829592227630525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6444523148878912607014733 2416696180829592227630525)
    ·
      refine ⟨906261067811097085361447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2416696180829592227630525 906261067811097085361447)
      ·
        refine ⟨1359391601716645628042171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 906261067811097085361447 1359391601716645628042171)
        ·
          refine ⟨2039087402574968442063257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1359391601716645628042171 2039087402574968442063257)
          ·
            refine ⟨1529315551931226331547443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2039087402574968442063257 1529315551931226331547443)
            ·
              refine ⟨2293973327896839497321165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1529315551931226331547443 2293973327896839497321165)
              ·
                refine ⟨860239997961314811495437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2293973327896839497321165 860239997961314811495437)
                ·
                  refine ⟨322589999235493054310789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 860239997961314811495437 322589999235493054310789)
                  ·
                    refine ⟨60485624856654947683273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 322589999235493054310789 60485624856654947683273)
                    ·
                      rfl

theorem cell22_176693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 3, 3, 4].length) (baseStart_176693 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_176693 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_176693 prefixEnd_176693 := by exact prefixLift 176693
  have htrace : WordTrace (prefixWord ++ tailWord_176693) baseStart_176693 baseEnd_176693 := by
    simpa [prefixWord, tailWord_176693, baseEnd_176693] using wordTrace_append hprefix tailTrace_176693
  have hstable : (prefixWord ++ tailWord_176693).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176693).length < 2 ^ (prefixWord ++ tailWord_176693).sum := by decide
  have hdescent : baseEnd_176693 < baseStart_176693 := by decide
  rcases family_descends (prefixWord ++ tailWord_176693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176725 : List Nat := [1, 3, 2, 2, 1, 1, 4, 4, 4]
def baseStart_176725 : Nat := 118140960795 + 176725 * 2 ^ 59
def prefixEnd_176725 : Nat := 4983230072969 + 3 ^ 40 * 176725 * 2
def baseEnd_176725 : Nat := 20165526370205843627725

theorem tailTrace_176725 : CollatzResearch.WordTrace tailWord_176725 prefixEnd_176725 20165526370205843627725 := by
  unfold tailWord_176725
  simp only [CollatzResearch.WordTrace]
  refine ⟨6445690284762982072179629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4297126856508654714786419 6445690284762982072179629)
  ·
    refine ⟨2417133856786118277067361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6445690284762982072179629 2417133856786118277067361)
    ·
      refine ⟨1812850392589588707800521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2417133856786118277067361 1812850392589588707800521)
      ·
        refine ⟨1359637794442191530850391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1812850392589588707800521 1359637794442191530850391)
        ·
          refine ⟨2039456691663287296275587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1359637794442191530850391 2039456691663287296275587)
          ·
            refine ⟨3059185037494930944413381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2039456691663287296275587 3059185037494930944413381)
            ·
              refine ⟨573597194530299552077509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3059185037494930944413381 573597194530299552077509)
              ·
                refine ⟨107549473974431166014533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 573597194530299552077509 107549473974431166014533)
                ·
                  refine ⟨20165526370205843627725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 107549473974431166014533 20165526370205843627725)
                  ·
                    rfl

theorem cell22_176725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 4, 4, 4].length) (baseStart_176725 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_176725 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_176725 prefixEnd_176725 := by exact prefixLift 176725
  have htrace : WordTrace (prefixWord ++ tailWord_176725) baseStart_176725 baseEnd_176725 := by
    simpa [prefixWord, tailWord_176725, baseEnd_176725] using wordTrace_append hprefix tailTrace_176725
  have hstable : (prefixWord ++ tailWord_176725).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176725).length < 2 ^ (prefixWord ++ tailWord_176725).sum := by decide
  have hdescent : baseEnd_176725 < baseStart_176725 := by decide
  rcases family_descends (prefixWord ++ tailWord_176725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176830 : List Nat := [4, 2, 1, 1, 2, 1, 2, 2, 2, 5]
def baseStart_176830 : Nat := 118140960795 + 176830 * 2 ^ 59
def prefixEnd_176830 : Nat := 4983230072969 + 3 ^ 40 * 176830 * 2
def baseEnd_176830 : Nat := 60532522756432257007853

theorem tailTrace_176830 : CollatzResearch.WordTrace tailWord_176830 prefixEnd_176830 60532522756432257007853 := by
  unfold tailWord_176830
  simp only [CollatzResearch.WordTrace]
  refine ⟨806189993672823125593993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4299679966255056669834629 806189993672823125593993)
  ·
    refine ⟨604642495254617344195495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 806189993672823125593993 604642495254617344195495)
    ·
      refine ⟨906963742881926016293243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 604642495254617344195495 906963742881926016293243)
      ·
        refine ⟨1360445614322889024439865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 906963742881926016293243 1360445614322889024439865)
        ·
          refine ⟨1020334210742166768329899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1360445614322889024439865 1020334210742166768329899)
          ·
            refine ⟨1530501316113250152494849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1020334210742166768329899 1530501316113250152494849)
            ·
              refine ⟨1147875987084937614371137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1530501316113250152494849 1147875987084937614371137)
              ·
                refine ⟨860906990313703210778353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1147875987084937614371137 860906990313703210778353)
                ·
                  refine ⟨645680242735277408083765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 860906990313703210778353 645680242735277408083765)
                  ·
                    refine ⟨60532522756432257007853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 645680242735277408083765 60532522756432257007853)
                    ·
                      rfl

theorem cell22_176830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 2, 2, 5].length) (baseStart_176830 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_176830 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_176830 prefixEnd_176830 := by exact prefixLift 176830
  have htrace : WordTrace (prefixWord ++ tailWord_176830) baseStart_176830 baseEnd_176830 := by
    simpa [prefixWord, tailWord_176830, baseEnd_176830] using wordTrace_append hprefix tailTrace_176830
  have hstable : (prefixWord ++ tailWord_176830).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176830).length < 2 ^ (prefixWord ++ tailWord_176830).sum := by decide
  have hdescent : baseEnd_176830 < baseStart_176830 := by decide
  rcases family_descends (prefixWord ++ tailWord_176830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176836 : List Nat := [2, 3, 3, 1, 1, 2, 4, 2, 1, 3]
def baseStart_176836 : Nat := 118140960795 + 176836 * 2 ^ 59
def prefixEnd_176836 : Nat := 4983230072969 + 3 ^ 40 * 176836 * 2
def baseEnd_176836 : Nat := 60534576679050241357835

theorem tailTrace_176836 : CollatzResearch.WordTrace tailWord_176836 prefixEnd_176836 60534576679050241357835 := by
  unfold tailWord_176836
  simp only [CollatzResearch.WordTrace]
  refine ⟨3224869393680424014735181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4299825858240565352980241 3224869393680424014735181)
  ·
    refine ⟨1209326022630159005525693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3224869393680424014735181 1209326022630159005525693)
    ·
      refine ⟨453497258486309627072135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1209326022630159005525693 453497258486309627072135)
      ·
        refine ⟨680245887729464440608203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 453497258486309627072135 680245887729464440608203)
        ·
          refine ⟨1020368831594196660912305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 680245887729464440608203 1020368831594196660912305)
          ·
            refine ⟨765276623695647495684229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1020368831594196660912305 765276623695647495684229)
            ·
              refine ⟨143489366942933905440793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 765276623695647495684229 143489366942933905440793)
              ·
                refine ⟨107617025207200429080595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 143489366942933905440793 107617025207200429080595)
                ·
                  refine ⟨161425537810800643620893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 107617025207200429080595 161425537810800643620893)
                  ·
                    refine ⟨60534576679050241357835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 161425537810800643620893 60534576679050241357835)
                    ·
                      rfl

theorem cell22_176836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 4, 2, 1, 3].length) (baseStart_176836 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_176836 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_176836 prefixEnd_176836 := by exact prefixLift 176836
  have htrace : WordTrace (prefixWord ++ tailWord_176836) baseStart_176836 baseEnd_176836 := by
    simpa [prefixWord, tailWord_176836, baseEnd_176836] using wordTrace_append hprefix tailTrace_176836
  have hstable : (prefixWord ++ tailWord_176836).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176836).length < 2 ^ (prefixWord ++ tailWord_176836).sum := by decide
  have hdescent : baseEnd_176836 < baseStart_176836 := by decide
  rcases family_descends (prefixWord ++ tailWord_176836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176875 : List Nat := [1, 1, 1, 1, 2, 4, 1, 4, 4, 3]
def baseStart_176875 : Nat := 118140960795 + 176875 * 2 ^ 59
def prefixEnd_176875 : Nat := 4983230072969 + 3 ^ 40 * 176875 * 2
def baseEnd_176875 : Nat := 60547927176067139632715

theorem tailTrace_176875 : CollatzResearch.WordTrace tailWord_176875 prefixEnd_176875 60547927176067139632715 := by
  unfold tailWord_176875
  simp only [CollatzResearch.WordTrace]
  refine ⟨6451161234219557690140079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4300774156146371793426719 6451161234219557690140079)
  ·
    refine ⟨9676741851329336535210119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6451161234219557690140079 9676741851329336535210119)
    ·
      refine ⟨14515112776994004802815179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9676741851329336535210119 14515112776994004802815179)
      ·
        refine ⟨21772669165491007204222769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14515112776994004802815179 21772669165491007204222769)
        ·
          refine ⟨16329501874118255403167077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21772669165491007204222769 16329501874118255403167077)
          ·
            refine ⟨3061781601397172888093827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16329501874118255403167077 3061781601397172888093827)
            ·
              refine ⟨4592672402095759332140741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3061781601397172888093827 4592672402095759332140741)
              ·
                refine ⟨861126075392954874776389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4592672402095759332140741 861126075392954874776389)
                ·
                  refine ⟨161461139136179039020573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 861126075392954874776389 161461139136179039020573)
                  ·
                    refine ⟨60547927176067139632715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 161461139136179039020573 60547927176067139632715)
                    ·
                      rfl

theorem cell22_176875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 4, 4, 3].length) (baseStart_176875 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_176875 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_176875 prefixEnd_176875 := by exact prefixLift 176875
  have htrace : WordTrace (prefixWord ++ tailWord_176875) baseStart_176875 baseEnd_176875 := by
    simpa [prefixWord, tailWord_176875, baseEnd_176875] using wordTrace_append hprefix tailTrace_176875
  have hstable : (prefixWord ++ tailWord_176875).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176875).length < 2 ^ (prefixWord ++ tailWord_176875).sum := by decide
  have hdescent : baseEnd_176875 < baseStart_176875 := by decide
  rcases family_descends (prefixWord ++ tailWord_176875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176879 : List Nat := [1, 1, 2, 1, 5, 4, 2, 1, 1, 4]
def baseStart_176879 : Nat := 118140960795 + 176879 * 2 ^ 59
def prefixEnd_176879 : Nat := 4983230072969 + 3 ^ 40 * 176879 * 2
def baseEnd_176879 : Nat := 60549296457812462532703

theorem tailTrace_176879 : CollatzResearch.WordTrace tailWord_176879 prefixEnd_176879 60549296457812462532703 := by
  unfold tailWord_176879
  simp only [CollatzResearch.WordTrace]
  refine ⟨6451307126205066373285691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4300871417470044248857127 6451307126205066373285691)
  ·
    refine ⟨9676960689307599559928537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6451307126205066373285691 9676960689307599559928537)
    ·
      refine ⟨7257720516980699669946403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9676960689307599559928537 7257720516980699669946403)
      ·
        refine ⟨10886580775471049504919605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7257720516980699669946403 10886580775471049504919605)
        ·
          refine ⟨1020616947700410891086213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10886580775471049504919605 1020616947700410891086213)
          ·
            refine ⟨191365677693827042078665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1020616947700410891086213 191365677693827042078665)
            ·
              refine ⟨143524258270370281558999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 191365677693827042078665 143524258270370281558999)
              ·
                refine ⟨215286387405555422338499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 143524258270370281558999 215286387405555422338499)
                ·
                  refine ⟨322929581108333133507749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 215286387405555422338499 322929581108333133507749)
                  ·
                    refine ⟨60549296457812462532703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 322929581108333133507749 60549296457812462532703)
                    ·
                      rfl

theorem cell22_176879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 2, 1, 1, 4].length) (baseStart_176879 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_176879 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_176879 prefixEnd_176879 := by exact prefixLift 176879
  have htrace : WordTrace (prefixWord ++ tailWord_176879) baseStart_176879 baseEnd_176879 := by
    simpa [prefixWord, tailWord_176879, baseEnd_176879] using wordTrace_append hprefix tailTrace_176879
  have hstable : (prefixWord ++ tailWord_176879).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176879).length < 2 ^ (prefixWord ++ tailWord_176879).sum := by decide
  have hdescent : baseEnd_176879 < baseStart_176879 := by decide
  rcases family_descends (prefixWord ++ tailWord_176879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176888 : List Nat := [2, 1, 2, 1, 1, 2, 13]
def baseStart_176888 : Nat := 118140960795 + 176888 * 2 ^ 59
def prefixEnd_176888 : Nat := 4983230072969 + 3 ^ 40 * 176888 * 2
def baseEnd_176888 : Nat := 2242680642286645891025

theorem tailTrace_176888 : CollatzResearch.WordTrace tailWord_176888 prefixEnd_176888 2242680642286645891025 := by
  unfold tailWord_176888
  simp only [CollatzResearch.WordTrace]
  refine ⟨3225817691586230455181659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4301090255448307273575545 3225817691586230455181659)
  ·
    refine ⟨4838726537379345682772489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3225817691586230455181659 4838726537379345682772489)
    ·
      refine ⟨3629044903034509262079367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4838726537379345682772489 3629044903034509262079367)
      ·
        refine ⟨5443567354551763893119051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3629044903034509262079367 5443567354551763893119051)
        ·
          refine ⟨8165351031827645839678577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5443567354551763893119051 8165351031827645839678577)
          ·
            refine ⟨6124013273870734379758933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8165351031827645839678577 6124013273870734379758933)
            ·
              refine ⟨2242680642286645891025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 6124013273870734379758933 2242680642286645891025)
              ·
                rfl

theorem cell22_176888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 13].length) (baseStart_176888 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_176888 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_176888 prefixEnd_176888 := by exact prefixLift 176888
  have htrace : WordTrace (prefixWord ++ tailWord_176888) baseStart_176888 baseEnd_176888 := by
    simpa [prefixWord, tailWord_176888, baseEnd_176888] using wordTrace_append hprefix tailTrace_176888
  have hstable : (prefixWord ++ tailWord_176888).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176888).length < 2 ^ (prefixWord ++ tailWord_176888).sum := by decide
  have hdescent : baseEnd_176888 < baseStart_176888 := by decide
  rcases family_descends (prefixWord ++ tailWord_176888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176890 : List Nat := [3, 1, 1, 1, 1, 3, 2, 4, 2, 4]
def baseStart_176890 : Nat := 118140960795 + 176890 * 2 ^ 59
def prefixEnd_176890 : Nat := 4983230072969 + 3 ^ 40 * 176890 * 2
def baseEnd_176890 : Nat := 60553061982612100507669

theorem tailTrace_176890 : CollatzResearch.WordTrace tailWord_176890 prefixEnd_176890 60553061982612100507669 := by
  unfold tailWord_176890
  simp only [CollatzResearch.WordTrace]
  refine ⟨1612927082291303812984031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4301138886110143501290749 1612927082291303812984031)
  ·
    refine ⟨2419390623436955719476047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1612927082291303812984031 2419390623436955719476047)
    ·
      refine ⟨3629085935155433579214071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2419390623436955719476047 3629085935155433579214071)
      ·
        refine ⟨5443628902733150368821107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3629085935155433579214071 5443628902733150368821107)
        ·
          refine ⟨8165443354099725553231661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5443628902733150368821107 8165443354099725553231661)
          ·
            refine ⟨3062041257787397082461873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8165443354099725553231661 3062041257787397082461873)
            ·
              refine ⟨2296530943340547811846405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3062041257787397082461873 2296530943340547811846405)
              ·
                refine ⟨430599551876352714721201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2296530943340547811846405 430599551876352714721201)
                ·
                  refine ⟨322949663907264536040901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 430599551876352714721201 322949663907264536040901)
                  ·
                    refine ⟨60553061982612100507669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 322949663907264536040901 60553061982612100507669)
                    ·
                      rfl

theorem cell22_176890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 4, 2, 4].length) (baseStart_176890 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_176890 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_176890 prefixEnd_176890 := by exact prefixLift 176890
  have htrace : WordTrace (prefixWord ++ tailWord_176890) baseStart_176890 baseEnd_176890 := by
    simpa [prefixWord, tailWord_176890, baseEnd_176890] using wordTrace_append hprefix tailTrace_176890
  have hstable : (prefixWord ++ tailWord_176890).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176890).length < 2 ^ (prefixWord ++ tailWord_176890).sum := by decide
  have hdescent : baseEnd_176890 < baseStart_176890 := by decide
  rcases family_descends (prefixWord ++ tailWord_176890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176892 : List Nat := [2, 2, 2, 1, 3, 3, 1, 1, 4, 3]
def baseStart_176892 : Nat := 118140960795 + 176892 * 2 ^ 59
def prefixEnd_176892 : Nat := 4983230072969 + 3 ^ 40 * 176892 * 2
def baseEnd_176892 : Nat := 60553746623484761957663

theorem tailTrace_176892 : CollatzResearch.WordTrace tailWord_176892 prefixEnd_176892 60553746623484761957663 := by
  unfold tailWord_176892
  simp only [CollatzResearch.WordTrace]
  refine ⟨3225890637578984796754465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4301187516771979729005953 3225890637578984796754465)
  ·
    refine ⟨2419417978184238597565849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3225890637578984796754465 2419417978184238597565849)
    ·
      refine ⟨1814563483638178948174387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2419417978184238597565849 1814563483638178948174387)
      ·
        refine ⟨2721845225457268422261581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1814563483638178948174387 2721845225457268422261581)
        ·
          refine ⟨1020691959546475658348093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2721845225457268422261581 1020691959546475658348093)
          ·
            refine ⟨382759484829928371880535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1020691959546475658348093 382759484829928371880535)
            ·
              refine ⟨574139227244892557820803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 382759484829928371880535 574139227244892557820803)
              ·
                refine ⟨861208840867338836731205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 574139227244892557820803 861208840867338836731205)
                ·
                  refine ⟨161476657662626031887101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 861208840867338836731205 161476657662626031887101)
                  ·
                    refine ⟨60553746623484761957663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 161476657662626031887101 60553746623484761957663)
                    ·
                      rfl

theorem cell22_176892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 1, 1, 4, 3].length) (baseStart_176892 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_176892 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_176892 prefixEnd_176892 := by exact prefixLift 176892
  have htrace : WordTrace (prefixWord ++ tailWord_176892) baseStart_176892 baseEnd_176892 := by
    simpa [prefixWord, tailWord_176892, baseEnd_176892] using wordTrace_append hprefix tailTrace_176892
  have hstable : (prefixWord ++ tailWord_176892).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176892).length < 2 ^ (prefixWord ++ tailWord_176892).sum := by decide
  have hdescent : baseEnd_176892 < baseStart_176892 := by decide
  rcases family_descends (prefixWord ++ tailWord_176892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176894 : List Nat := [4, 2, 2, 1, 2, 1, 2, 4, 4]
def baseStart_176894 : Nat := 118140960795 + 176894 * 2 ^ 59
def prefixEnd_176894 : Nat := 4983230072969 + 3 ^ 40 * 176894 * 2
def baseEnd_176894 : Nat := 20184810421452474469219

theorem tailTrace_176894 : CollatzResearch.WordTrace tailWord_176894 prefixEnd_176894 20184810421452474469219 := by
  unfold tailWord_176894
  simp only [CollatzResearch.WordTrace]
  refine ⟨806481777643840491885217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4301236147433815956721157 806481777643840491885217)
  ·
    refine ⟨604861333232880368913913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 806481777643840491885217 604861333232880368913913)
    ·
      refine ⟨453645999924660276685435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 604861333232880368913913 453645999924660276685435)
      ·
        refine ⟨680468999886990415028153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 453645999924660276685435 680468999886990415028153)
        ·
          refine ⟨510351749915242811271115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 680468999886990415028153 510351749915242811271115)
          ·
            refine ⟨765527624872864216906673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 510351749915242811271115 765527624872864216906673)
            ·
              refine ⟨574145718654648162680005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 765527624872864216906673 574145718654648162680005)
              ·
                refine ⟨107652322247746530502501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 574145718654648162680005 107652322247746530502501)
                ·
                  refine ⟨20184810421452474469219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 107652322247746530502501 20184810421452474469219)
                  ·
                    rfl

theorem cell22_176894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 2, 4, 4].length) (baseStart_176894 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_176894 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_176894 prefixEnd_176894 := by exact prefixLift 176894
  have htrace : WordTrace (prefixWord ++ tailWord_176894) baseStart_176894 baseEnd_176894 := by
    simpa [prefixWord, tailWord_176894, baseEnd_176894] using wordTrace_append hprefix tailTrace_176894
  have hstable : (prefixWord ++ tailWord_176894).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176894).length < 2 ^ (prefixWord ++ tailWord_176894).sum := by decide
  have hdescent : baseEnd_176894 < baseStart_176894 := by decide
  rcases family_descends (prefixWord ++ tailWord_176894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176941 : List Nat := [1, 5, 3, 2, 1, 1, 1, 2, 2, 4]
def baseStart_176941 : Nat := 118140960795 + 176941 * 2 ^ 59
def prefixEnd_176941 : Nat := 4983230072969 + 3 ^ 40 * 176941 * 2
def baseEnd_176941 : Nat := 60570520324864967482513

theorem tailTrace_176941 : CollatzResearch.WordTrace tailWord_176941 prefixEnd_176941 60570520324864967482513 := by
  unfold tailWord_176941
  simp only [CollatzResearch.WordTrace]
  refine ⟨6453568451980450962042677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4302378967986967308028451 6453568451980450962042677)
  ·
    refine ⟨605022042373167277691501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6453568451980450962042677 605022042373167277691501)
    ·
      refine ⟨226883265889937729134313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 605022042373167277691501 226883265889937729134313)
      ·
        refine ⟨170162449417453296850735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 226883265889937729134313 170162449417453296850735)
        ·
          refine ⟨255243674126179945276103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170162449417453296850735 255243674126179945276103)
          ·
            refine ⟨382865511189269917914155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 255243674126179945276103 382865511189269917914155)
            ·
              refine ⟨574298266783904876871233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 382865511189269917914155 574298266783904876871233)
              ·
                refine ⟨430723700087928657653425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 574298266783904876871233 430723700087928657653425)
                ·
                  refine ⟨323042775065946493240069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 430723700087928657653425 323042775065946493240069)
                  ·
                    refine ⟨60570520324864967482513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 323042775065946493240069 60570520324864967482513)
                    ·
                      rfl

theorem cell22_176941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 1, 2, 2, 4].length) (baseStart_176941 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_176941 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_176941 prefixEnd_176941 := by exact prefixLift 176941
  have htrace : WordTrace (prefixWord ++ tailWord_176941) baseStart_176941 baseEnd_176941 := by
    simpa [prefixWord, tailWord_176941, baseEnd_176941] using wordTrace_append hprefix tailTrace_176941
  have hstable : (prefixWord ++ tailWord_176941).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176941).length < 2 ^ (prefixWord ++ tailWord_176941).sum := by decide
  have hdescent : baseEnd_176941 < baseStart_176941 := by decide
  rcases family_descends (prefixWord ++ tailWord_176941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176997 : List Nat := [1, 3, 1, 3, 1, 1, 2, 5, 1, 4]
def baseStart_176997 : Nat := 118140960795 + 176997 * 2 ^ 59
def prefixEnd_176997 : Nat := 4983230072969 + 3 ^ 40 * 176997 * 2
def baseEnd_176997 : Nat := 60589690269299488082341

theorem tailTrace_176997 : CollatzResearch.WordTrace tailWord_176997 prefixEnd_176997 60589690269299488082341 := by
  unfold tailWord_176997
  simp only [CollatzResearch.WordTrace]
  refine ⟨6455610939777572526081245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4303740626518381684054163 6455610939777572526081245)
  ·
    refine ⟨2420854102416589697280467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6455610939777572526081245 2420854102416589697280467)
    ·
      refine ⟨3631281153624884545920701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2420854102416589697280467 3631281153624884545920701)
      ·
        refine ⟨1361730432609331704720263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3631281153624884545920701 1361730432609331704720263)
        ·
          refine ⟨2042595648913997557080395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1361730432609331704720263 2042595648913997557080395)
          ·
            refine ⟨3063893473370996335620593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2042595648913997557080395 3063893473370996335620593)
            ·
              refine ⟨2297920105028247251715445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3063893473370996335620593 2297920105028247251715445)
              ·
                refine ⟨215430009846398179848323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2297920105028247251715445 215430009846398179848323)
                ·
                  refine ⟨323145014769597269772485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 215430009846398179848323 323145014769597269772485)
                  ·
                    refine ⟨60589690269299488082341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 323145014769597269772485 60589690269299488082341)
                    ·
                      rfl

theorem cell22_176997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 5, 1, 4].length) (baseStart_176997 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_176997 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_176997 prefixEnd_176997 := by exact prefixLift 176997
  have htrace : WordTrace (prefixWord ++ tailWord_176997) baseStart_176997 baseEnd_176997 := by
    simpa [prefixWord, tailWord_176997, baseEnd_176997] using wordTrace_append hprefix tailTrace_176997
  have hstable : (prefixWord ++ tailWord_176997).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176997).length < 2 ^ (prefixWord ++ tailWord_176997).sum := by decide
  have hdescent : baseEnd_176997 < baseStart_176997 := by decide
  rcases family_descends (prefixWord ++ tailWord_176997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_177014 : List Nat := [5, 1, 1, 3, 1, 1, 1, 2, 3, 4]
def baseStart_177014 : Nat := 118140960795 + 177014 * 2 ^ 59
def prefixEnd_177014 : Nat := 4983230072969 + 3 ^ 40 * 177014 * 2
def baseEnd_177014 : Nat := 60595509716717110407289

theorem tailTrace_177014 : CollatzResearch.WordTrace tailWord_177014 prefixEnd_177014 60595509716717110407289 := by
  unfold tailWord_177014
  simp only [CollatzResearch.WordTrace]
  refine ⟨403514436294749026840631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4304153987143989619633397 403514436294749026840631)
  ·
    refine ⟨605271654442123540260947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 403514436294749026840631 605271654442123540260947)
    ·
      refine ⟨907907481663185310391421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 605271654442123540260947 907907481663185310391421)
      ·
        refine ⟨340465305623694491396783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 907907481663185310391421 340465305623694491396783)
        ·
          refine ⟨510697958435541737095175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 340465305623694491396783 510697958435541737095175)
          ·
            refine ⟨766046937653312605642763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 510697958435541737095175 766046937653312605642763)
            ·
              refine ⟨1149070406479968908464145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 766046937653312605642763 1149070406479968908464145)
              ·
                refine ⟨861802804859976681348109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1149070406479968908464145 861802804859976681348109)
                ·
                  refine ⟨323176051822491255505541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 861802804859976681348109 323176051822491255505541)
                  ·
                    refine ⟨60595509716717110407289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 323176051822491255505541 60595509716717110407289)
                    ·
                      rfl

theorem cell22_177014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 2, 3, 4].length) (baseStart_177014 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_177014 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_177014 prefixEnd_177014 := by exact prefixLift 177014
  have htrace : WordTrace (prefixWord ++ tailWord_177014) baseStart_177014 baseEnd_177014 := by
    simpa [prefixWord, tailWord_177014, baseEnd_177014] using wordTrace_append hprefix tailTrace_177014
  have hstable : (prefixWord ++ tailWord_177014).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_177014).length < 2 ^ (prefixWord ++ tailWord_177014).sum := by decide
  have hdescent : baseEnd_177014 < baseStart_177014 := by decide
  rcases family_descends (prefixWord ++ tailWord_177014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_177027 : List Nat := [1, 1, 1, 3, 4, 1, 4, 1, 1, 5]
def baseStart_177027 : Nat := 118140960795 + 177027 * 2 ^ 59
def prefixEnd_177027 : Nat := 4983230072969 + 3 ^ 40 * 177027 * 2
def baseEnd_177027 : Nat := 60599959882389409832249

theorem tailTrace_177027 : CollatzResearch.WordTrace tailWord_177027 prefixEnd_177027 60599959882389409832249 := by
  unfold tailWord_177027
  simp only [CollatzResearch.WordTrace]
  refine ⟨6456705129668887649673335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4304470086445925099782223 6456705129668887649673335)
  ·
    refine ⟨9685057694503331474510003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6456705129668887649673335 9685057694503331474510003)
    ·
      refine ⟨14527586541754997211765005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9685057694503331474510003 14527586541754997211765005)
      ·
        refine ⟨5447844953158123954411877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14527586541754997211765005 5447844953158123954411877)
        ·
          refine ⟨1021470928717148241452227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5447844953158123954411877 1021470928717148241452227)
          ·
            refine ⟨1532206393075722362178341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1021470928717148241452227 1532206393075722362178341)
            ·
              refine ⟨287288698701697942908439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1532206393075722362178341 287288698701697942908439)
              ·
                refine ⟨430933048052546914362659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 287288698701697942908439 430933048052546914362659)
                ·
                  refine ⟨646399572078820371543989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 430933048052546914362659 646399572078820371543989)
                  ·
                    refine ⟨60599959882389409832249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 646399572078820371543989 60599959882389409832249)
                    ·
                      rfl

theorem cell22_177027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 4, 1, 1, 5].length) (baseStart_177027 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_177027 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_177027 prefixEnd_177027 := by exact prefixLift 177027
  have htrace : WordTrace (prefixWord ++ tailWord_177027) baseStart_177027 baseEnd_177027 := by
    simpa [prefixWord, tailWord_177027, baseEnd_177027] using wordTrace_append hprefix tailTrace_177027
  have hstable : (prefixWord ++ tailWord_177027).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_177027).length < 2 ^ (prefixWord ++ tailWord_177027).sum := by decide
  have hdescent : baseEnd_177027 < baseStart_177027 := by decide
  rcases family_descends (prefixWord ++ tailWord_177027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_177044 : List Nat := [2, 4, 2, 1, 1, 1, 2, 2, 4, 3]
def baseStart_177044 : Nat := 118140960795 + 177044 * 2 ^ 59
def prefixEnd_177044 : Nat := 4983230072969 + 3 ^ 40 * 177044 * 2
def baseEnd_177044 : Nat := 60605779329807032157197

theorem tailTrace_177044 : CollatzResearch.WordTrace tailWord_177044 prefixEnd_177044 60605779329807032157197 := by
  unfold tailWord_177044
  simp only [CollatzResearch.WordTrace]
  refine ⟨3228662585303649776521093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4304883447071533035361457 3228662585303649776521093)
  ·
    refine ⟨605374234744434333097705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3228662585303649776521093 605374234744434333097705)
    ·
      refine ⟨454030676058325749823279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 605374234744434333097705 454030676058325749823279)
      ·
        refine ⟨681046014087488624734919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 454030676058325749823279 681046014087488624734919)
        ·
          refine ⟨1021569021131232937102379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 681046014087488624734919 1021569021131232937102379)
          ·
            refine ⟨1532353531696849405653569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1021569021131232937102379 1532353531696849405653569)
            ·
              refine ⟨1149265148772637054240177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1532353531696849405653569 1149265148772637054240177)
              ·
                refine ⟨861948861579477790680133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1149265148772637054240177 861948861579477790680133)
                ·
                  refine ⟨161615411546152085752525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 861948861579477790680133 161615411546152085752525)
                  ·
                    refine ⟨60605779329807032157197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 161615411546152085752525 60605779329807032157197)
                    ·
                      rfl

theorem cell22_177044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 2, 4, 3].length) (baseStart_177044 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_177044 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_177044 prefixEnd_177044 := by exact prefixLift 177044
  have htrace : WordTrace (prefixWord ++ tailWord_177044) baseStart_177044 baseEnd_177044 := by
    simpa [prefixWord, tailWord_177044, baseEnd_177044] using wordTrace_append hprefix tailTrace_177044
  have hstable : (prefixWord ++ tailWord_177044).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_177044).length < 2 ^ (prefixWord ++ tailWord_177044).sum := by decide
  have hdescent : baseEnd_177044 < baseStart_177044 := by decide
  rcases family_descends (prefixWord ++ tailWord_177044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_177057 : List Nat := [1, 2, 3, 4, 1, 2, 9]
def baseStart_177057 : Nat := 118140960795 + 177057 * 2 ^ 59
def prefixEnd_177057 : Nat := 4983230072969 + 3 ^ 40 * 177057 * 2
def baseEnd_177057 : Nat := 2244823314647382651191

theorem tailTrace_177057 : CollatzResearch.WordTrace tailWord_177057 prefixEnd_177057 2244823314647382651191 := by
  unfold tailWord_177057
  simp only [CollatzResearch.WordTrace]
  refine ⟨6457799319560202773265425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4305199546373468515510283 6457799319560202773265425)
  ·
    refine ⟨4843349489670152079949069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6457799319560202773265425 4843349489670152079949069)
    ·
      refine ⟨1816256058626307029980901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4843349489670152079949069 1816256058626307029980901)
      ·
        refine ⟨340548010992432568121419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1816256058626307029980901 340548010992432568121419)
        ·
          refine ⟨510822016488648852182129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 340548010992432568121419 510822016488648852182129)
          ·
            refine ⟨383116512366486639136597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 510822016488648852182129 383116512366486639136597)
            ·
              refine ⟨2244823314647382651191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 383116512366486639136597 2244823314647382651191)
              ·
                rfl

theorem cell22_177057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 9].length) (baseStart_177057 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_177057 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_177057 prefixEnd_177057 := by exact prefixLift 177057
  have htrace : WordTrace (prefixWord ++ tailWord_177057) baseStart_177057 baseEnd_177057 := by
    simpa [prefixWord, tailWord_177057, baseEnd_177057] using wordTrace_append hprefix tailTrace_177057
  have hstable : (prefixWord ++ tailWord_177057).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_177057).length < 2 ^ (prefixWord ++ tailWord_177057).sum := by decide
  have hdescent : baseEnd_177057 < baseStart_177057 := by decide
  rcases family_descends (prefixWord ++ tailWord_177057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_177102 : List Nat := [4, 1, 1, 1, 2, 3, 1, 2, 7]
def baseStart_177102 : Nat := 118140960795 + 177102 * 2 ^ 59
def prefixEnd_177102 : Nat := 4983230072969 + 3 ^ 40 * 177102 * 2
def baseEnd_177102 : Nat := 20208544638371404735673

theorem tailTrace_177102 : CollatzResearch.WordTrace tailWord_177102 prefixEnd_177102 20208544638371404735673 := by
  unfold tailWord_177102
  simp only [CollatzResearch.WordTrace]
  refine ⟨807430075549646932331695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4306293736264783639102373 807430075549646932331695)
  ·
    refine ⟨1211145113324470398497543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 807430075549646932331695 1211145113324470398497543)
    ·
      refine ⟨1816717669986705597746315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1211145113324470398497543 1816717669986705597746315)
      ·
        refine ⟨2725076504980058396619473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1816717669986705597746315 2725076504980058396619473)
        ·
          refine ⟨2043807378735043797464605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2725076504980058396619473 2043807378735043797464605)
          ·
            refine ⟨766427767025641424049227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2043807378735043797464605 766427767025641424049227)
            ·
              refine ⟨1149641650538462136073841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 766427767025641424049227 1149641650538462136073841)
              ·
                refine ⟨862231237903846602055381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1149641650538462136073841 862231237903846602055381)
                ·
                  refine ⟨20208544638371404735673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 862231237903846602055381 20208544638371404735673)
                  ·
                    rfl

theorem cell22_177102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 2, 7].length) (baseStart_177102 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_177102 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_177102 prefixEnd_177102 := by exact prefixLift 177102
  have htrace : WordTrace (prefixWord ++ tailWord_177102) baseStart_177102 baseEnd_177102 := by
    simpa [prefixWord, tailWord_177102, baseEnd_177102] using wordTrace_append hprefix tailTrace_177102
  have hstable : (prefixWord ++ tailWord_177102).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_177102).length < 2 ^ (prefixWord ++ tailWord_177102).sum := by decide
  have hdescent : baseEnd_177102 < baseStart_177102 := by decide
  rcases family_descends (prefixWord ++ tailWord_177102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_177123 : List Nat := [1, 1, 1, 6, 1, 1, 5, 2, 1, 3]
def baseStart_177123 : Nat := 118140960795 + 177123 * 2 ^ 59
def prefixEnd_177123 : Nat := 4983230072969 + 3 ^ 40 * 177123 * 2
def baseEnd_177123 : Nat := 60632822644277159431955

theorem tailTrace_177123 : CollatzResearch.WordTrace tailWord_177123 prefixEnd_177123 60632822644277159431955 := by
  unfold tailWord_177123
  simp only [CollatzResearch.WordTrace]
  refine ⟨6460206537321096045168023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4306804358214064030112015 6460206537321096045168023)
  ·
    refine ⟨9690309805981644067752035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6460206537321096045168023 9690309805981644067752035)
    ·
      refine ⟨14535464708972466101628053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9690309805981644067752035 14535464708972466101628053)
      ·
        refine ⟨681349908233084348513815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 14535464708972466101628053 681349908233084348513815)
        ·
          refine ⟨1022024862349626522770723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 681349908233084348513815 1022024862349626522770723)
          ·
            refine ⟨1533037293524439784156085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1022024862349626522770723 1533037293524439784156085)
            ·
              refine ⟨143722246267916229764633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1533037293524439784156085 143722246267916229764633)
              ·
                refine ⟨107791684700937172323475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 143722246267916229764633 107791684700937172323475)
                ·
                  refine ⟨161687527051405758485213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 107791684700937172323475 161687527051405758485213)
                  ·
                    refine ⟨60632822644277159431955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 161687527051405758485213 60632822644277159431955)
                    ·
                      rfl

theorem cell22_177123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 5, 2, 1, 3].length) (baseStart_177123 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_177123 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_177123 prefixEnd_177123 := by exact prefixLift 177123
  have htrace : WordTrace (prefixWord ++ tailWord_177123) baseStart_177123 baseEnd_177123 := by
    simpa [prefixWord, tailWord_177123, baseEnd_177123] using wordTrace_append hprefix tailTrace_177123
  have hstable : (prefixWord ++ tailWord_177123).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_177123).length < 2 ^ (prefixWord ++ tailWord_177123).sum := by decide
  have hdescent : baseEnd_177123 < baseStart_177123 := by decide
  rcases family_descends (prefixWord ++ tailWord_177123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_177170 : List Nat := [3, 2, 5, 1, 1, 1, 2, 2, 5]
def baseStart_177170 : Nat := 118140960795 + 177170 * 2 ^ 59
def prefixEnd_177170 : Nat := 4983230072969 + 3 ^ 40 * 177170 * 2
def baseEnd_177170 : Nat := 20216303901594901168937

theorem tailTrace_177170 : CollatzResearch.WordTrace tailWord_177170 prefixEnd_177170 20216303901594901168937 := by
  unfold tailWord_177170
  simp only [CollatzResearch.WordTrace]
  refine ⟨1615480192037705768032241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4307947178767215381419309 1615480192037705768032241)
  ·
    refine ⟨1211610144028279326024181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1615480192037705768032241 1211610144028279326024181)
    ·
      refine ⟨113588451002651186814767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1211610144028279326024181 113588451002651186814767)
      ·
        refine ⟨170382676503976780222151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113588451002651186814767 170382676503976780222151)
        ·
          refine ⟨255574014755965170333227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170382676503976780222151 255574014755965170333227)
          ·
            refine ⟨383361022133947755499841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 255574014755965170333227 383361022133947755499841)
            ·
              refine ⟨287520766600460816624881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 383361022133947755499841 287520766600460816624881)
              ·
                refine ⟨215640574950345612468661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 287520766600460816624881 215640574950345612468661)
                ·
                  refine ⟨20216303901594901168937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 215640574950345612468661 20216303901594901168937)
                  ·
                    rfl

theorem cell22_177170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 2, 2, 5].length) (baseStart_177170 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_177170 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_177170 prefixEnd_177170 := by exact prefixLift 177170
  have htrace : WordTrace (prefixWord ++ tailWord_177170) baseStart_177170 baseEnd_177170 := by
    simpa [prefixWord, tailWord_177170, baseEnd_177170] using wordTrace_append hprefix tailTrace_177170
  have hstable : (prefixWord ++ tailWord_177170).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_177170).length < 2 ^ (prefixWord ++ tailWord_177170).sum := by decide
  have hdescent : baseEnd_177170 < baseStart_177170 := by decide
  rcases family_descends (prefixWord ++ tailWord_177170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_177224 : List Nat := [2, 1, 3, 1, 1, 1, 3, 2, 5, 3]
def baseStart_177224 : Nat := 118140960795 + 177224 * 2 ^ 59
def prefixEnd_177224 : Nat := 4983230072969 + 3 ^ 40 * 177224 * 2
def baseEnd_177224 : Nat := 60667397008346562656645

theorem tailTrace_177224 : CollatzResearch.WordTrace tailWord_177224 prefixEnd_177224 60667397008346562656645 := by
  unfold tailWord_177224
  simp only [CollatzResearch.WordTrace]
  refine ⟨3231945154977595147297363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4309260206636793529729817 3231945154977595147297363)
  ·
    refine ⟨4847917732466392720946045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3231945154977595147297363 4847917732466392720946045)
    ·
      refine ⟨1817969149674897270354767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4847917732466392720946045 1817969149674897270354767)
      ·
        refine ⟨2726953724512345905532151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1817969149674897270354767 2726953724512345905532151)
        ·
          refine ⟨4090430586768518858298227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2726953724512345905532151 4090430586768518858298227)
          ·
            refine ⟨6135645880152778287447341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4090430586768518858298227 6135645880152778287447341)
            ·
              refine ⟨2300867205057291857792753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6135645880152778287447341 2300867205057291857792753)
              ·
                refine ⟨1725650403792968893344565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2300867205057291857792753 1725650403792968893344565)
                ·
                  refine ⟨161779725355590833751053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1725650403792968893344565 161779725355590833751053)
                  ·
                    refine ⟨60667397008346562656645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 161779725355590833751053 60667397008346562656645)
                    ·
                      rfl

theorem cell22_177224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 2, 5, 3].length) (baseStart_177224 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_177224 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_177224 prefixEnd_177224 := by exact prefixLift 177224
  have htrace : WordTrace (prefixWord ++ tailWord_177224) baseStart_177224 baseEnd_177224 := by
    simpa [prefixWord, tailWord_177224, baseEnd_177224] using wordTrace_append hprefix tailTrace_177224
  have hstable : (prefixWord ++ tailWord_177224).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_177224).length < 2 ^ (prefixWord ++ tailWord_177224).sum := by decide
  have hdescent : baseEnd_177224 < baseStart_177224 := by decide
  rcases family_descends (prefixWord ++ tailWord_177224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_177267 : List Nat := [1, 1, 1, 2, 2, 1, 1, 1, 4, 8]
def baseStart_177267 : Nat := 118140960795 + 177267 * 2 ^ 59
def prefixEnd_177267 : Nat := 4983230072969 + 3 ^ 40 * 177267 * 2
def baseEnd_177267 : Nat := 60682116787108783831513

theorem tailTrace_177267 : CollatzResearch.WordTrace tailWord_177267 prefixEnd_177267 60682116787108783831513 := by
  unfold tailWord_177267
  simp only [CollatzResearch.WordTrace]
  refine ⟨6465458648799408638410055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4310305765866272425606703 6465458648799408638410055)
  ·
    refine ⟨9698187973199112957615083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6465458648799408638410055 9698187973199112957615083)
    ·
      refine ⟨14547281959798669436422625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9698187973199112957615083 14547281959798669436422625)
      ·
        refine ⟨10910461469849002077316969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14547281959798669436422625 10910461469849002077316969)
        ·
          refine ⟨8182846102386751557987727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10910461469849002077316969 8182846102386751557987727)
          ·
            refine ⟨12274269153580127336981591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8182846102386751557987727 12274269153580127336981591)
            ·
              refine ⟨18411403730370191005472387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12274269153580127336981591 18411403730370191005472387)
              ·
                refine ⟨27617105595555286508208581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18411403730370191005472387 27617105595555286508208581)
                ·
                  refine ⟨5178207299166616220289109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27617105595555286508208581 5178207299166616220289109)
                  ·
                    refine ⟨60682116787108783831513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 5178207299166616220289109 60682116787108783831513)
                    ·
                      rfl

theorem cell22_177267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 4, 8].length) (baseStart_177267 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_177267 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_177267 prefixEnd_177267 := by exact prefixLift 177267
  have htrace : WordTrace (prefixWord ++ tailWord_177267) baseStart_177267 baseEnd_177267 := by
    simpa [prefixWord, tailWord_177267, baseEnd_177267] using wordTrace_append hprefix tailTrace_177267
  have hstable : (prefixWord ++ tailWord_177267).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_177267).length < 2 ^ (prefixWord ++ tailWord_177267).sum := by decide
  have hdescent : baseEnd_177267 < baseStart_177267 := by decide
  rcases family_descends (prefixWord ++ tailWord_177267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_177299 : List Nat := [1, 1, 1, 2, 1, 2, 7, 1, 6]
def baseStart_177299 : Nat := 118140960795 + 177299 * 2 ^ 59
def prefixEnd_177299 : Nat := 4983230072969 + 3 ^ 40 * 177299 * 2
def baseEnd_177299 : Nat := 20231023680357122343805

theorem tailTrace_177299 : CollatzResearch.WordTrace tailWord_177299 prefixEnd_177299 20231023680357122343805 := by
  unfold tailWord_177299
  simp only [CollatzResearch.WordTrace]
  refine ⟨6466625784683478103574951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4311083856455652069049967 6466625784683478103574951)
  ·
    refine ⟨9699938677025217155362427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6466625784683478103574951 9699938677025217155362427)
    ·
      refine ⟨14549908015537825733043641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9699938677025217155362427 14549908015537825733043641)
      ·
        refine ⟨10912431011653369299782731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14549908015537825733043641 10912431011653369299782731)
        ·
          refine ⟨16368646517480053949674097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10912431011653369299782731 16368646517480053949674097)
          ·
            refine ⟨12276484888110040462255573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16368646517480053949674097 12276484888110040462255573)
            ·
              refine ⟨287730114565079073334115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 12276484888110040462255573 287730114565079073334115)
              ·
                refine ⟨431595171847618610001173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 287730114565079073334115 431595171847618610001173)
                ·
                  refine ⟨20231023680357122343805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 431595171847618610001173 20231023680357122343805)
                  ·
                    rfl

theorem cell22_177299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 7, 1, 6].length) (baseStart_177299 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_177299 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_177299 prefixEnd_177299 := by exact prefixLift 177299
  have htrace : WordTrace (prefixWord ++ tailWord_177299) baseStart_177299 baseEnd_177299 := by
    simpa [prefixWord, tailWord_177299, baseEnd_177299] using wordTrace_append hprefix tailTrace_177299
  have hstable : (prefixWord ++ tailWord_177299).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_177299).length < 2 ^ (prefixWord ++ tailWord_177299).sum := by decide
  have hdescent : baseEnd_177299 < baseStart_177299 := by decide
  rcases family_descends (prefixWord ++ tailWord_177299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_177344 : List Nat := [2, 1, 1, 2, 6, 10]
def baseStart_177344 : Nat := 118140960795 + 177344 * 2 ^ 59
def prefixEnd_177344 : Nat := 4983230072969 + 3 ^ 40 * 177344 * 2
def baseEnd_177344 : Nat := 749487351366743822917

theorem tailTrace_177344 : CollatzResearch.WordTrace tailWord_177344 prefixEnd_177344 749487351366743822917 := by
  unfold tailWord_177344
  simp only [CollatzResearch.WordTrace]
  refine ⟨3234133534760225394481543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4312178046346967192642057 3234133534760225394481543)
  ·
    refine ⟨4851200302140338091722315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3234133534760225394481543 4851200302140338091722315)
    ·
      refine ⟨7276800453210507137583473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4851200302140338091722315 7276800453210507137583473)
      ·
        refine ⟨5457600339907880353187605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7276800453210507137583473 5457600339907880353187605)
        ·
          refine ⟨255825015933181891555669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 5457600339907880353187605 255825015933181891555669)
          ·
            refine ⟨749487351366743822917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 255825015933181891555669 749487351366743822917)
            ·
              rfl

theorem cell22_177344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 10].length) (baseStart_177344 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_177344 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_177344 prefixEnd_177344 := by exact prefixLift 177344
  have htrace : WordTrace (prefixWord ++ tailWord_177344) baseStart_177344 baseEnd_177344 := by
    simpa [prefixWord, tailWord_177344, baseEnd_177344] using wordTrace_append hprefix tailTrace_177344
  have hstable : (prefixWord ++ tailWord_177344).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_177344).length < 2 ^ (prefixWord ++ tailWord_177344).sum := by decide
  have hdescent : baseEnd_177344 < baseStart_177344 := by decide
  rcases family_descends (prefixWord ++ tailWord_177344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_177376 : List Nat := [2, 1, 1, 3, 1, 4, 1, 1, 5, 3]
def baseStart_177376 : Nat := 118140960795 + 177376 * 2 ^ 59
def prefixEnd_177376 : Nat := 4983230072969 + 3 ^ 40 * 177376 * 2
def baseEnd_177376 : Nat := 60719429714668832856179

theorem tailTrace_177376 : CollatzResearch.WordTrace tailWord_177376 prefixEnd_177376 60719429714668832856179 := by
  unfold tailWord_177376
  simp only [CollatzResearch.WordTrace]
  refine ⟨3234717102702260127063991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4312956136936346836085321 3234717102702260127063991)
  ·
    refine ⟨4852075654053390190595987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3234717102702260127063991 4852075654053390190595987)
    ·
      refine ⟨7278113481080085285893981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4852075654053390190595987 7278113481080085285893981)
      ·
        refine ⟨2729292555405031982210243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7278113481080085285893981 2729292555405031982210243)
        ·
          refine ⟨4093938833107547973315365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2729292555405031982210243 4093938833107547973315365)
          ·
            refine ⟨767613531207665244996631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4093938833107547973315365 767613531207665244996631)
            ·
              refine ⟨1151420296811497867494947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 767613531207665244996631 1151420296811497867494947)
              ·
                refine ⟨1727130445217246801242421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1151420296811497867494947 1727130445217246801242421)
                ·
                  refine ⟨161918479239116887616477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1727130445217246801242421 161918479239116887616477)
                  ·
                    refine ⟨60719429714668832856179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 161918479239116887616477 60719429714668832856179)
                    ·
                      rfl

theorem cell22_177376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 1, 5, 3].length) (baseStart_177376 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_177376 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_177376 prefixEnd_177376 := by exact prefixLift 177376
  have htrace : WordTrace (prefixWord ++ tailWord_177376) baseStart_177376 baseEnd_177376 := by
    simpa [prefixWord, tailWord_177376, baseEnd_177376] using wordTrace_append hprefix tailTrace_177376
  have hstable : (prefixWord ++ tailWord_177376).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_177376).length < 2 ^ (prefixWord ++ tailWord_177376).sum := by decide
  have hdescent : baseEnd_177376 < baseStart_177376 := by decide
  rcases family_descends (prefixWord ++ tailWord_177376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_177436 : List Nat := [2, 2, 3, 1, 1, 1, 2, 3, 3, 4]
def baseStart_177436 : Nat := 118140960795 + 177436 * 2 ^ 59
def prefixEnd_177436 : Nat := 4983230072969 + 3 ^ 40 * 177436 * 2
def baseEnd_177436 : Nat := 60739968940848676355995

theorem tailTrace_177436 : CollatzResearch.WordTrace tailWord_177436 prefixEnd_177436 60739968940848676355995 := by
  unfold tailWord_177436
  simp only [CollatzResearch.WordTrace]
  refine ⟨3235811292593575250656081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4314415056791433667541441 3235811292593575250656081)
  ·
    refine ⟨2426858469445181437992061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3235811292593575250656081 2426858469445181437992061)
    ·
      refine ⟨910071926041943039247023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2426858469445181437992061 910071926041943039247023)
      ·
        refine ⟨1365107889062914558870535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 910071926041943039247023 1365107889062914558870535)
        ·
          refine ⟨2047661833594371838305803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1365107889062914558870535 2047661833594371838305803)
          ·
            refine ⟨3071492750391557757458705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2047661833594371838305803 3071492750391557757458705)
            ·
              refine ⟨2303619562793668318094029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3071492750391557757458705 2303619562793668318094029)
              ·
                refine ⟨863857336047625619285261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2303619562793668318094029 863857336047625619285261)
                ·
                  refine ⟨323946501017859607231973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 863857336047625619285261 323946501017859607231973)
                  ·
                    refine ⟨60739968940848676355995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 323946501017859607231973 60739968940848676355995)
                    ·
                      rfl

theorem cell22_177436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 3, 3, 4].length) (baseStart_177436 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_177436 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_177436 prefixEnd_177436 := by exact prefixLift 177436
  have htrace : WordTrace (prefixWord ++ tailWord_177436) baseStart_177436 baseEnd_177436 := by
    simpa [prefixWord, tailWord_177436, baseEnd_177436] using wordTrace_append hprefix tailTrace_177436
  have hstable : (prefixWord ++ tailWord_177436).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_177436).length < 2 ^ (prefixWord ++ tailWord_177436).sum := by decide
  have hdescent : baseEnd_177436 < baseStart_177436 := by decide
  rcases family_descends (prefixWord ++ tailWord_177436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_177468 : List Nat := [2, 2, 2, 2, 1, 5, 1, 1, 6]
def baseStart_177468 : Nat := 118140960795 + 177468 * 2 ^ 59
def prefixEnd_177468 : Nat := 4983230072969 + 3 ^ 40 * 177468 * 2
def baseEnd_177468 : Nat := 20250307731603753185299

theorem tailTrace_177468 : CollatzResearch.WordTrace tailWord_177468 prefixEnd_177468 20250307731603753185299 := by
  unfold tailWord_177468
  simp only [CollatzResearch.WordTrace]
  refine ⟨3236394860535609983238529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4315193147380813310984705 3236394860535609983238529)
  ·
    refine ⟨2427296145401707487428897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3236394860535609983238529 2427296145401707487428897)
    ·
      refine ⟨1820472109051280615571673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2427296145401707487428897 1820472109051280615571673)
      ·
        refine ⟨1365354081788460461678755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1820472109051280615571673 1365354081788460461678755)
        ·
          refine ⟨2048031122682690692518133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1365354081788460461678755 2048031122682690692518133)
          ·
            refine ⟨192002917751502252423575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2048031122682690692518133 192002917751502252423575)
            ·
              refine ⟨288004376627253378635363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 192002917751502252423575 288004376627253378635363)
              ·
                refine ⟨432006564940880067953045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 288004376627253378635363 432006564940880067953045)
                ·
                  refine ⟨20250307731603753185299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 432006564940880067953045 20250307731603753185299)
                  ·
                    rfl

theorem cell22_177468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 1, 1, 6].length) (baseStart_177468 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_177468 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_177468 prefixEnd_177468 := by exact prefixLift 177468
  have htrace : WordTrace (prefixWord ++ tailWord_177468) baseStart_177468 baseEnd_177468 := by
    simpa [prefixWord, tailWord_177468, baseEnd_177468] using wordTrace_append hprefix tailTrace_177468
  have hstable : (prefixWord ++ tailWord_177468).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_177468).length < 2 ^ (prefixWord ++ tailWord_177468).sum := by decide
  have hdescent : baseEnd_177468 < baseStart_177468 := by decide
  rcases family_descends (prefixWord ++ tailWord_177468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_177545 : List Nat := [1, 2, 1, 1, 7, 1, 1, 2, 3, 3]
def baseStart_177545 : Nat := 118140960795 + 177545 * 2 ^ 59
def prefixEnd_177545 : Nat := 4983230072969 + 3 ^ 40 * 177545 * 2
def baseEnd_177545 : Nat := 60777281868408725380661

theorem tailTrace_177545 : CollatzResearch.WordTrace tailWord_177545 prefixEnd_177545 60777281868408725380661 := by
  unfold tailWord_177545
  simp only [CollatzResearch.WordTrace]
  refine ⟨6475598141792262117030089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4317065427861508078020059 6475598141792262117030089)
  ·
    refine ⟨4856698606344196587772567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6475598141792262117030089 4856698606344196587772567)
    ·
      refine ⟨7285047909516294881658851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4856698606344196587772567 7285047909516294881658851)
      ·
        refine ⟨10927571864274442322488277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7285047909516294881658851 10927571864274442322488277)
        ·
          refine ⟨256114965568932241933319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 10927571864274442322488277 256114965568932241933319)
          ·
            refine ⟨384172448353398362899979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 256114965568932241933319 384172448353398362899979)
            ·
              refine ⟨576258672530097544349969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 384172448353398362899979 576258672530097544349969)
              ·
                refine ⟨432194004397573158262477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 576258672530097544349969 432194004397573158262477)
                ·
                  refine ⟨162072751649089934348429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 432194004397573158262477 162072751649089934348429)
                  ·
                    refine ⟨60777281868408725380661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 162072751649089934348429 60777281868408725380661)
                    ·
                      rfl

theorem cell22_177545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 1, 2, 3, 3].length) (baseStart_177545 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_177545 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_177545 prefixEnd_177545 := by exact prefixLift 177545
  have htrace : WordTrace (prefixWord ++ tailWord_177545) baseStart_177545 baseEnd_177545 := by
    simpa [prefixWord, tailWord_177545, baseEnd_177545] using wordTrace_append hprefix tailTrace_177545
  have hstable : (prefixWord ++ tailWord_177545).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_177545).length < 2 ^ (prefixWord ++ tailWord_177545).sum := by decide
  have hdescent : baseEnd_177545 < baseStart_177545 := by decide
  rcases family_descends (prefixWord ++ tailWord_177545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_177562 : List Nat := [3, 1, 1, 4, 1, 1, 4, 3, 1, 3]
def baseStart_177562 : Nat := 118140960795 + 177562 * 2 ^ 59
def prefixEnd_177562 : Nat := 4983230072969 + 3 ^ 40 * 177562 * 2
def baseEnd_177562 : Nat := 60783101315826347705609

theorem tailTrace_177562 : CollatzResearch.WordTrace tailWord_177562 prefixEnd_177562 60783101315826347705609 := by
  unfold tailWord_177562
  simp only [CollatzResearch.WordTrace]
  refine ⟨1619054545682668505099735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4317478788487116013599293 1619054545682668505099735)
  ·
    refine ⟨2428581818524002757649603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1619054545682668505099735 2428581818524002757649603)
    ·
      refine ⟨3642872727786004136474405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2428581818524002757649603 3642872727786004136474405)
      ·
        refine ⟨683038636459875775588951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3642872727786004136474405 683038636459875775588951)
        ·
          refine ⟨1024557954689813663383427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 683038636459875775588951 1024557954689813663383427)
          ·
            refine ⟨1536836932034720495075141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1024557954689813663383427 1536836932034720495075141)
            ·
              refine ⟨288156924756510092826589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1536836932034720495075141 288156924756510092826589)
              ·
                refine ⟨108058846783691284809971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 288156924756510092826589 108058846783691284809971)
                ·
                  refine ⟨162088270175536927214957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 108058846783691284809971 162088270175536927214957)
                  ·
                    refine ⟨60783101315826347705609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 162088270175536927214957 60783101315826347705609)
                    ·
                      rfl

theorem cell22_177562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 4, 3, 1, 3].length) (baseStart_177562 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_177562 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_177562 prefixEnd_177562 := by exact prefixLift 177562
  have htrace : WordTrace (prefixWord ++ tailWord_177562) baseStart_177562 baseEnd_177562 := by
    simpa [prefixWord, tailWord_177562, baseEnd_177562] using wordTrace_append hprefix tailTrace_177562
  have hstable : (prefixWord ++ tailWord_177562).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_177562).length < 2 ^ (prefixWord ++ tailWord_177562).sum := by decide
  have hdescent : baseEnd_177562 < baseStart_177562 := by decide
  rcases family_descends (prefixWord ++ tailWord_177562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_177622 : List Nat := [5, 2, 1, 1, 1, 2, 2, 3, 1, 4]
def baseStart_177622 : Nat := 118140960795 + 177622 * 2 ^ 59
def prefixEnd_177622 : Nat := 4983230072969 + 3 ^ 40 * 177622 * 2
def baseEnd_177622 : Nat := 60803640542006191205425

theorem tailTrace_177622 : CollatzResearch.WordTrace tailWord_177622 prefixEnd_177622 60803640542006191205425 := by
  unfold tailWord_177622
  simp only [CollatzResearch.WordTrace]
  refine ⟨404900410157081516723945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4318937708342202845055413 404900410157081516723945)
  ·
    refine ⟨303675307617811137542959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 404900410157081516723945 303675307617811137542959)
    ·
      refine ⟨455512961426716706314439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 303675307617811137542959 455512961426716706314439)
      ·
        refine ⟨683269442140075059471659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 455512961426716706314439 683269442140075059471659)
        ·
          refine ⟨1024904163210112589207489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 683269442140075059471659 1024904163210112589207489)
          ·
            refine ⟨768678122407584441905617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1024904163210112589207489 768678122407584441905617)
            ·
              refine ⟨576508591805688331429213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 768678122407584441905617 576508591805688331429213)
              ·
                refine ⟨216190721927133124285955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 576508591805688331429213 216190721927133124285955)
                ·
                  refine ⟨324286082890699686428933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 216190721927133124285955 324286082890699686428933)
                  ·
                    refine ⟨60803640542006191205425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 324286082890699686428933 60803640542006191205425)
                    ·
                      rfl

theorem cell22_177622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 2, 3, 1, 4].length) (baseStart_177622 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_177622 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_177622 prefixEnd_177622 := by exact prefixLift 177622
  have htrace : WordTrace (prefixWord ++ tailWord_177622) baseStart_177622 baseEnd_177622 := by
    simpa [prefixWord, tailWord_177622, baseEnd_177622] using wordTrace_append hprefix tailTrace_177622
  have hstable : (prefixWord ++ tailWord_177622).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_177622).length < 2 ^ (prefixWord ++ tailWord_177622).sum := by decide
  have hdescent : baseEnd_177622 < baseStart_177622 := by decide
  rcases family_descends (prefixWord ++ tailWord_177622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_177633 : List Nat := [1, 2, 3, 1, 2, 3, 1, 1, 4, 4]
def baseStart_177633 : Nat := 118140960795 + 177633 * 2 ^ 59
def prefixEnd_177633 : Nat := 4983230072969 + 3 ^ 40 * 177633 * 2
def baseEnd_177633 : Nat := 60807406066805829180391

theorem tailTrace_177633 : CollatzResearch.WordTrace tailWord_177633 prefixEnd_177633 60807406066805829180391 := by
  unfold tailWord_177633
  simp only [CollatzResearch.WordTrace]
  refine ⟨6478807765473453146233553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4319205176982302097489035 6478807765473453146233553)
  ·
    refine ⟨4859105824105089859675165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6478807765473453146233553 4859105824105089859675165)
    ·
      refine ⟨1822164684039408697378187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4859105824105089859675165 1822164684039408697378187)
      ·
        refine ⟨2733247026059113046067281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1822164684039408697378187 2733247026059113046067281)
        ·
          refine ⟨2049935269544334784550461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2733247026059113046067281 2049935269544334784550461)
          ·
            refine ⟨768725726079125544206423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2049935269544334784550461 768725726079125544206423)
            ·
              refine ⟨1153088589118688316309635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 768725726079125544206423 1153088589118688316309635)
              ·
                refine ⟨1729632883678032474464453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1153088589118688316309635 1729632883678032474464453)
                ·
                  refine ⟨324306165689631088962085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1729632883678032474464453 324306165689631088962085)
                  ·
                    refine ⟨60807406066805829180391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 324306165689631088962085 60807406066805829180391)
                    ·
                      rfl

theorem cell22_177633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 1, 4, 4].length) (baseStart_177633 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_177633 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_177633 prefixEnd_177633 := by exact prefixLift 177633
  have htrace : WordTrace (prefixWord ++ tailWord_177633) baseStart_177633 baseEnd_177633 := by
    simpa [prefixWord, tailWord_177633, baseEnd_177633] using wordTrace_append hprefix tailTrace_177633
  have hstable : (prefixWord ++ tailWord_177633).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_177633).length < 2 ^ (prefixWord ++ tailWord_177633).sum := by decide
  have hdescent : baseEnd_177633 < baseStart_177633 := by decide
  rcases family_descends (prefixWord ++ tailWord_177633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_177635 : List Nat := [1, 1, 1, 6, 2, 1, 2, 1, 4, 3]
def baseStart_177635 : Nat := 118140960795 + 177635 * 2 ^ 59
def prefixEnd_177635 : Nat := 4983230072969 + 3 ^ 40 * 177635 * 2
def baseEnd_177635 : Nat := 60808090707678490630385

theorem tailTrace_177635 : CollatzResearch.WordTrace tailWord_177635 prefixEnd_177635 60808090707678490630385 := by
  unfold tailWord_177635
  simp only [CollatzResearch.WordTrace]
  refine ⟨6478880711466207487806359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4319253807644138325204239 6478880711466207487806359)
  ·
    refine ⟨9718321067199311231709539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6478880711466207487806359 9718321067199311231709539)
    ·
      refine ⟨14577481600798966847564309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9718321067199311231709539 14577481600798966847564309)
      ·
        refine ⟨683319450037451570979577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 14577481600798966847564309 683319450037451570979577)
        ·
          refine ⟨512489587528088678234683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 683319450037451570979577 512489587528088678234683)
          ·
            refine ⟨768734381292133017352025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 512489587528088678234683 768734381292133017352025)
            ·
              refine ⟨576550785969099763014019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 768734381292133017352025 576550785969099763014019)
              ·
                refine ⟨864826178953649644521029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 576550785969099763014019 864826178953649644521029)
                ·
                  refine ⟨162154908553809308347693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 864826178953649644521029 162154908553809308347693)
                  ·
                    refine ⟨60808090707678490630385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 162154908553809308347693 60808090707678490630385)
                    ·
                      rfl

theorem cell22_177635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 2, 1, 4, 3].length) (baseStart_177635 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_177635 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_177635 prefixEnd_177635 := by exact prefixLift 177635
  have htrace : WordTrace (prefixWord ++ tailWord_177635) baseStart_177635 baseEnd_177635 := by
    simpa [prefixWord, tailWord_177635, baseEnd_177635] using wordTrace_append hprefix tailTrace_177635
  have hstable : (prefixWord ++ tailWord_177635).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_177635).length < 2 ^ (prefixWord ++ tailWord_177635).sum := by decide
  have hdescent : baseEnd_177635 < baseStart_177635 := by decide
  rcases family_descends (prefixWord ++ tailWord_177635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_177648 : List Nat := [2, 1, 1, 1, 3, 5, 2, 7]
def baseStart_177648 : Nat := 118140960795 + 177648 * 2 ^ 59
def prefixEnd_177648 : Nat := 4983230072969 + 3 ^ 40 * 177648 * 2
def baseEnd_177648 : Nat := 6756948985927865561705

theorem tailTrace_177648 : CollatzResearch.WordTrace tailWord_177648 prefixEnd_177648 6756948985927865561705 := by
  unfold tailWord_177648
  simp only [CollatzResearch.WordTrace]
  refine ⟨3239677430209555354014799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4319569906946073805353065 3239677430209555354014799)
  ·
    refine ⟨4859516145314333031022199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3239677430209555354014799 4859516145314333031022199)
    ·
      refine ⟨7289274217971499546533299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4859516145314333031022199 7289274217971499546533299)
      ·
        refine ⟨10933911326957249319799949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7289274217971499546533299 10933911326957249319799949)
        ·
          refine ⟨4100216747608968494924981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10933911326957249319799949 4100216747608968494924981)
          ·
            refine ⟨384395320088340796399217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4100216747608968494924981 384395320088340796399217)
            ·
              refine ⟨288296490066255597299413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 384395320088340796399217 288296490066255597299413)
              ·
                refine ⟨6756948985927865561705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 288296490066255597299413 6756948985927865561705)
                ·
                  rfl

theorem cell22_177648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 2, 7].length) (baseStart_177648 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_177648 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_177648 prefixEnd_177648 := by exact prefixLift 177648
  have htrace : WordTrace (prefixWord ++ tailWord_177648) baseStart_177648 baseEnd_177648 := by
    simpa [prefixWord, tailWord_177648, baseEnd_177648] using wordTrace_append hprefix tailTrace_177648
  have hstable : (prefixWord ++ tailWord_177648).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_177648).length < 2 ^ (prefixWord ++ tailWord_177648).sum := by decide
  have hdescent : baseEnd_177648 < baseStart_177648 := by decide
  rcases family_descends (prefixWord ++ tailWord_177648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_177738 : List Nat := [3, 1, 2, 1, 1, 3, 1, 2, 8]
def baseStart_177738 : Nat := 118140960795 + 177738 * 2 ^ 59
def prefixEnd_177738 : Nat := 4983230072969 + 3 ^ 40 * 177738 * 2
def baseEnd_177738 : Nat := 20281116570873518435023

theorem tailTrace_177738 : CollatzResearch.WordTrace tailWord_177738 prefixEnd_177738 20281116570873518435023 := by
  unfold tailWord_177738
  simp only [CollatzResearch.WordTrace]
  refine ⟨1620659357523264019701467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4321758286728704052537245 1620659357523264019701467)
  ·
    refine ⟨2430989036284896029552201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1620659357523264019701467 2430989036284896029552201)
    ·
      refine ⟨1823241777213672022164151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2430989036284896029552201 1823241777213672022164151)
      ·
        refine ⟨2734862665820508033246227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1823241777213672022164151 2734862665820508033246227)
        ·
          refine ⟨4102293998730762049869341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2734862665820508033246227 4102293998730762049869341)
          ·
            refine ⟨1538360249524035768701003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4102293998730762049869341 1538360249524035768701003)
            ·
              refine ⟨2307540374286053653051505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1538360249524035768701003 2307540374286053653051505)
              ·
                refine ⟨1730655280714540239788629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2307540374286053653051505 1730655280714540239788629)
                ·
                  refine ⟨20281116570873518435023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1730655280714540239788629 20281116570873518435023)
                  ·
                    rfl

theorem cell22_177738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 2, 8].length) (baseStart_177738 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_177738 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_177738 prefixEnd_177738 := by exact prefixLift 177738
  have htrace : WordTrace (prefixWord ++ tailWord_177738) baseStart_177738 baseEnd_177738 := by
    simpa [prefixWord, tailWord_177738, baseEnd_177738] using wordTrace_append hprefix tailTrace_177738
  have hstable : (prefixWord ++ tailWord_177738).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_177738).length < 2 ^ (prefixWord ++ tailWord_177738).sum := by decide
  have hdescent : baseEnd_177738 < baseStart_177738 := by decide
  rcases family_descends (prefixWord ++ tailWord_177738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_177753 : List Nat := [1, 2, 1, 2, 2, 1, 1, 4, 3, 5]
def baseStart_177753 : Nat := 118140960795 + 177753 * 2 ^ 59
def prefixEnd_177753 : Nat := 4983230072969 + 3 ^ 40 * 177753 * 2
def baseEnd_177753 : Nat := 60848484519165516180023

theorem tailTrace_177753 : CollatzResearch.WordTrace tailWord_177753 prefixEnd_177753 60848484519165516180023 := by
  unfold tailWord_177753
  simp only [CollatzResearch.WordTrace]
  refine ⟨6483184525038713640601913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4322123016692475760401275 6483184525038713640601913)
  ·
    refine ⟨4862388393779035230451435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6483184525038713640601913 4862388393779035230451435)
    ·
      refine ⟨7293582590668552845677153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4862388393779035230451435 7293582590668552845677153)
      ·
        refine ⟨5470186943001414634257865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7293582590668552845677153 5470186943001414634257865)
        ·
          refine ⟨4102640207251060975693399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5470186943001414634257865 4102640207251060975693399)
          ·
            refine ⟨6153960310876591463540099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4102640207251060975693399 6153960310876591463540099)
            ·
              refine ⟨9230940466314887195310149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6153960310876591463540099 9230940466314887195310149)
              ·
                refine ⟨1730801337434041349120653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9230940466314887195310149 1730801337434041349120653)
                ·
                  refine ⟨649050501537765505920245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1730801337434041349120653 649050501537765505920245)
                  ·
                    refine ⟨60848484519165516180023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 649050501537765505920245 60848484519165516180023)
                    ·
                      rfl

theorem cell22_177753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 4, 3, 5].length) (baseStart_177753 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_177753 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_177753 prefixEnd_177753 := by exact prefixLift 177753
  have htrace : WordTrace (prefixWord ++ tailWord_177753) baseStart_177753 baseEnd_177753 := by
    simpa [prefixWord, tailWord_177753, baseEnd_177753] using wordTrace_append hprefix tailTrace_177753
  have hstable : (prefixWord ++ tailWord_177753).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_177753).length < 2 ^ (prefixWord ++ tailWord_177753).sum := by decide
  have hdescent : baseEnd_177753 < baseStart_177753 := by decide
  rcases family_descends (prefixWord ++ tailWord_177753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_177774 : List Nat := [4, 1, 2, 2, 3, 1, 2, 2, 1, 4]
def baseStart_177774 : Nat := 118140960795 + 177774 * 2 ^ 59
def prefixEnd_177774 : Nat := 4983230072969 + 3 ^ 40 * 177774 * 2
def baseEnd_177774 : Nat := 60855673248328461404959

theorem tailTrace_177774 : CollatzResearch.WordTrace tailWord_177774 prefixEnd_177774 60855673248328461404959 := by
  unfold tailWord_177774
  simp only [CollatzResearch.WordTrace]
  refine ⟨810493807245329278389547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4322633638641756151410917 810493807245329278389547)
  ·
    refine ⟨1215740710867993917584321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 810493807245329278389547 1215740710867993917584321)
    ·
      refine ⟨911805533150995438188241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1215740710867993917584321 911805533150995438188241)
      ·
        refine ⟨683854149863246578641181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 911805533150995438188241 683854149863246578641181)
        ·
          refine ⟨256445306198717466990443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 683854149863246578641181 256445306198717466990443)
          ·
            refine ⟨384667959298076200485665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 256445306198717466990443 384667959298076200485665)
            ·
              refine ⟨288500969473557150364249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 384667959298076200485665 288500969473557150364249)
              ·
                refine ⟨216375727105167862773187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 288500969473557150364249 216375727105167862773187)
                ·
                  refine ⟨324563590657751794159781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 216375727105167862773187 324563590657751794159781)
                  ·
                    refine ⟨60855673248328461404959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 324563590657751794159781 60855673248328461404959)
                    ·
                      rfl

theorem cell22_177774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 2, 2, 1, 4].length) (baseStart_177774 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_177774 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_177774 prefixEnd_177774 := by exact prefixLift 177774
  have htrace : WordTrace (prefixWord ++ tailWord_177774) baseStart_177774 baseEnd_177774 := by
    simpa [prefixWord, tailWord_177774, baseEnd_177774] using wordTrace_append hprefix tailTrace_177774
  have hstable : (prefixWord ++ tailWord_177774).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_177774).length < 2 ^ (prefixWord ++ tailWord_177774).sum := by decide
  have hdescent : baseEnd_177774 < baseStart_177774 := by decide
  rcases family_descends (prefixWord ++ tailWord_177774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_177785 : List Nat := [1, 2, 1, 3, 3, 1, 2, 3, 2, 4]
def baseStart_177785 : Nat := 118140960795 + 177785 * 2 ^ 59
def prefixEnd_177785 : Nat := 4983230072969 + 3 ^ 40 * 177785 * 2
def baseEnd_177785 : Nat := 60859438773128099379925

theorem tailTrace_177785 : CollatzResearch.WordTrace tailWord_177785 prefixEnd_177785 60859438773128099379925 := by
  unfold tailWord_177785
  simp only [CollatzResearch.WordTrace]
  refine ⟨6484351660922783105766809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4322901107281855403844539 6484351660922783105766809)
  ·
    refine ⟨4863263745692087329325107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6484351660922783105766809 4863263745692087329325107)
    ·
      refine ⟨7294895618538130993987661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4863263745692087329325107 7294895618538130993987661)
      ·
        refine ⟨2735585856951799122745373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7294895618538130993987661 2735585856951799122745373)
        ·
          refine ⟨1025844696356924671029515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2735585856951799122745373 1025844696356924671029515)
          ·
            refine ⟨1538767044535387006544273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1025844696356924671029515 1538767044535387006544273)
            ·
              refine ⟨1154075283401540254908205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1538767044535387006544273 1154075283401540254908205)
              ·
                refine ⟨432778231275577595590577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1154075283401540254908205 432778231275577595590577)
                ·
                  refine ⟨324583673456683196692933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 432778231275577595590577 324583673456683196692933)
                  ·
                    refine ⟨60859438773128099379925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 324583673456683196692933 60859438773128099379925)
                    ·
                      rfl

theorem cell22_177785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 3, 2, 4].length) (baseStart_177785 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_177785 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_177785 prefixEnd_177785 := by exact prefixLift 177785
  have htrace : WordTrace (prefixWord ++ tailWord_177785) baseStart_177785 baseEnd_177785 := by
    simpa [prefixWord, tailWord_177785, baseEnd_177785] using wordTrace_append hprefix tailTrace_177785
  have hstable : (prefixWord ++ tailWord_177785).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_177785).length < 2 ^ (prefixWord ++ tailWord_177785).sum := by decide
  have hdescent : baseEnd_177785 < baseStart_177785 := by decide
  rcases family_descends (prefixWord ++ tailWord_177785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_177789 : List Nat := [1, 4, 1, 1, 4, 3, 1, 3, 4]
def baseStart_177789 : Nat := 118140960795 + 177789 * 2 ^ 59
def prefixEnd_177789 : Nat := 4983230072969 + 3 ^ 40 * 177789 * 2
def baseEnd_177789 : Nat := 20286936018291140759971

theorem tailTrace_177789 : CollatzResearch.WordTrace tailWord_177789 prefixEnd_177789 20286936018291140759971 := by
  unfold tailWord_177789
  simp only [CollatzResearch.WordTrace]
  refine ⟨6484497552908291788912421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4322998368605527859274947 6484497552908291788912421)
  ·
    refine ⟨1215843291170304710421079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6484497552908291788912421 1215843291170304710421079)
    ·
      refine ⟨1823764936755457065631619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1215843291170304710421079 1823764936755457065631619)
      ·
        refine ⟨2735647405133185598447429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1823764936755457065631619 2735647405133185598447429)
        ·
          refine ⟨512933888462472299708893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2735647405133185598447429 512933888462472299708893)
          ·
            refine ⟨192350208173427112390835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 512933888462472299708893 192350208173427112390835)
            ·
              refine ⟨288525312260140668586253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 192350208173427112390835 288525312260140668586253)
              ·
                refine ⟨108196992097552750719845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 288525312260140668586253 108196992097552750719845)
                ·
                  refine ⟨20286936018291140759971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 108196992097552750719845 20286936018291140759971)
                  ·
                    rfl

theorem cell22_177789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 1, 3, 4].length) (baseStart_177789 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_177789 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_177789 prefixEnd_177789 := by exact prefixLift 177789
  have htrace : WordTrace (prefixWord ++ tailWord_177789) baseStart_177789 baseEnd_177789 := by
    simpa [prefixWord, tailWord_177789, baseEnd_177789] using wordTrace_append hprefix tailTrace_177789
  have hstable : (prefixWord ++ tailWord_177789).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_177789).length < 2 ^ (prefixWord ++ tailWord_177789).sum := by decide
  have hdescent : baseEnd_177789 < baseStart_177789 := by decide
  rcases family_descends (prefixWord ++ tailWord_177789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_177802 : List Nat := [3, 1, 2, 3, 2, 2, 1, 2, 2, 4]
def baseStart_177802 : Nat := 118140960795 + 177802 * 2 ^ 59
def prefixEnd_177802 : Nat := 4983230072969 + 3 ^ 40 * 177802 * 2
def baseEnd_177802 : Nat := 60865258220545721704873

theorem tailTrace_177802 : CollatzResearch.WordTrace tailWord_177802 prefixEnd_177802 60865258220545721704873 := by
  unfold tailWord_177802
  simp only [CollatzResearch.WordTrace]
  refine ⟨1621242925465298752283915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4323314467907463339423773 1621242925465298752283915)
  ·
    refine ⟨2431864388197948128425873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1621242925465298752283915 2431864388197948128425873)
    ·
      refine ⟨1823898291148461096319405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2431864388197948128425873 1823898291148461096319405)
      ·
        refine ⟨683961859180672911119777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1823898291148461096319405 683961859180672911119777)
        ·
          refine ⟨512971394385504683339833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 683961859180672911119777 512971394385504683339833)
          ·
            refine ⟨384728545789128512504875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 512971394385504683339833 384728545789128512504875)
            ·
              refine ⟨577092818683692768757313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 384728545789128512504875 577092818683692768757313)
              ·
                refine ⟨432819614012769576567985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 577092818683692768757313 432819614012769576567985)
                ·
                  refine ⟨324614710509577182425989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 432819614012769576567985 324614710509577182425989)
                  ·
                    refine ⟨60865258220545721704873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 324614710509577182425989 60865258220545721704873)
                    ·
                      rfl

theorem cell22_177802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 1, 2, 2, 4].length) (baseStart_177802 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_177802 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_177802 prefixEnd_177802 := by exact prefixLift 177802
  have htrace : WordTrace (prefixWord ++ tailWord_177802) baseStart_177802 baseEnd_177802 := by
    simpa [prefixWord, tailWord_177802, baseEnd_177802] using wordTrace_append hprefix tailTrace_177802
  have hstable : (prefixWord ++ tailWord_177802).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_177802).length < 2 ^ (prefixWord ++ tailWord_177802).sum := by decide
  have hdescent : baseEnd_177802 < baseStart_177802 := by decide
  rcases family_descends (prefixWord ++ tailWord_177802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_177866 : List Nat := [3, 1, 2, 1, 5, 1, 1, 4, 1, 3]
def baseStart_177866 : Nat := 118140960795 + 177866 * 2 ^ 59
def prefixEnd_177866 : Nat := 4983230072969 + 3 ^ 40 * 177866 * 2
def baseEnd_177866 : Nat := 60887166728470888104677

theorem tailTrace_177866 : CollatzResearch.WordTrace tailWord_177866 prefixEnd_177866 60887166728470888104677 := by
  unfold tailWord_177866
  simp only [CollatzResearch.WordTrace]
  refine ⟨1621826493407333484866363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4324870649086222626310301 1621826493407333484866363)
  ·
    refine ⟨2432739740111000227299545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1621826493407333484866363 2432739740111000227299545)
    ·
      refine ⟨1824554805083250170474659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2432739740111000227299545 1824554805083250170474659)
      ·
        refine ⟨2736832207624875255711989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1824554805083250170474659 2736832207624875255711989)
        ·
          refine ⟨256578019464832055222999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2736832207624875255711989 256578019464832055222999)
          ·
            refine ⟨384867029197248082834499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 256578019464832055222999 384867029197248082834499)
            ·
              refine ⟨577300543795872124251749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 384867029197248082834499 577300543795872124251749)
              ·
                refine ⟨108243851961726023297203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 577300543795872124251749 108243851961726023297203)
                ·
                  refine ⟨162365777942589034945805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 108243851961726023297203 162365777942589034945805)
                  ·
                    refine ⟨60887166728470888104677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 162365777942589034945805 60887166728470888104677)
                    ·
                      rfl

theorem cell22_177866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 1, 4, 1, 3].length) (baseStart_177866 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_177866 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_177866 prefixEnd_177866 := by exact prefixLift 177866
  have htrace : WordTrace (prefixWord ++ tailWord_177866) baseStart_177866 baseEnd_177866 := by
    simpa [prefixWord, tailWord_177866, baseEnd_177866] using wordTrace_append hprefix tailTrace_177866
  have hstable : (prefixWord ++ tailWord_177866).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_177866).length < 2 ^ (prefixWord ++ tailWord_177866).sum := by decide
  have hdescent : baseEnd_177866 < baseStart_177866 := by decide
  rcases family_descends (prefixWord ++ tailWord_177866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_177892 : List Nat := [2, 3, 1, 1, 1, 3, 2, 4, 1, 4]
def baseStart_177892 : Nat := 118140960795 + 177892 * 2 ^ 59
def prefixEnd_177892 : Nat := 4983230072969 + 3 ^ 40 * 177892 * 2
def baseEnd_177892 : Nat := 60896067059815486954597

theorem tailTrace_177892 : CollatzResearch.WordTrace tailWord_177892 prefixEnd_177892 60896067059815486954597 := by
  unfold tailWord_177892
  simp only [CollatzResearch.WordTrace]
  refine ⟨3244127135767570189955965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4325502847690093586607953 3244127135767570189955965)
  ·
    refine ⟨1216547675912838821233487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3244127135767570189955965 1216547675912838821233487)
    ·
      refine ⟨1824821513869258231850231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1216547675912838821233487 1824821513869258231850231)
      ·
        refine ⟨2737232270803887347775347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1824821513869258231850231 2737232270803887347775347)
        ·
          refine ⟨4105848406205831021663021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2737232270803887347775347 4105848406205831021663021)
          ·
            refine ⟨1539693152327186633123633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4105848406205831021663021 1539693152327186633123633)
            ·
              refine ⟨1154769864245389974842725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1539693152327186633123633 1154769864245389974842725)
              ·
                refine ⟨216519349546010620283011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1154769864245389974842725 216519349546010620283011)
                ·
                  refine ⟨324779024319015930424517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 216519349546010620283011 324779024319015930424517)
                  ·
                    refine ⟨60896067059815486954597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 324779024319015930424517 60896067059815486954597)
                    ·
                      rfl

theorem cell22_177892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 4, 1, 4].length) (baseStart_177892 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_177892 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_177892 prefixEnd_177892 := by exact prefixLift 177892
  have htrace : WordTrace (prefixWord ++ tailWord_177892) baseStart_177892 baseEnd_177892 := by
    simpa [prefixWord, tailWord_177892, baseEnd_177892] using wordTrace_append hprefix tailTrace_177892
  have hstable : (prefixWord ++ tailWord_177892).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_177892).length < 2 ^ (prefixWord ++ tailWord_177892).sum := by decide
  have hdescent : baseEnd_177892 < baseStart_177892 := by decide
  rcases family_descends (prefixWord ++ tailWord_177892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_177907 : List Nat := [1, 1, 1, 2, 2, 3, 3, 5, 4]
def baseStart_177907 : Nat := 118140960795 + 177907 * 2 ^ 59
def prefixEnd_177907 : Nat := 4983230072969 + 3 ^ 40 * 177907 * 2
def baseEnd_177907 : Nat := 20300400622120149276517

theorem tailTrace_177907 : CollatzResearch.WordTrace tailWord_177907 prefixEnd_177907 20300400622120149276517 := by
  unfold tailWord_177907
  simp only [CollatzResearch.WordTrace]
  refine ⟨6488801366480797941707975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4325867577653865294471983 6488801366480797941707975)
  ·
    refine ⟨9733202049721196912561963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6488801366480797941707975 9733202049721196912561963)
    ·
      refine ⟨14599803074581795368842945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9733202049721196912561963 14599803074581795368842945)
      ·
        refine ⟨10949852305936346526632209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14599803074581795368842945 10949852305936346526632209)
        ·
          refine ⟨8212389229452259894974157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10949852305936346526632209 8212389229452259894974157)
          ·
            refine ⟨3079645961044597460615309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8212389229452259894974157 3079645961044597460615309)
            ·
              refine ⟨1154867235391724047730741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3079645961044597460615309 1154867235391724047730741)
              ·
                refine ⟨108268803317974129474757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1154867235391724047730741 108268803317974129474757)
                ·
                  refine ⟨20300400622120149276517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 108268803317974129474757 20300400622120149276517)
                  ·
                    rfl

theorem cell22_177907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 5, 4].length) (baseStart_177907 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_177907 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_177907 prefixEnd_177907 := by exact prefixLift 177907
  have htrace : WordTrace (prefixWord ++ tailWord_177907) baseStart_177907 baseEnd_177907 := by
    simpa [prefixWord, tailWord_177907, baseEnd_177907] using wordTrace_append hprefix tailTrace_177907
  have hstable : (prefixWord ++ tailWord_177907).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_177907).length < 2 ^ (prefixWord ++ tailWord_177907).sum := by decide
  have hdescent : baseEnd_177907 < baseStart_177907 := by decide
  rcases family_descends (prefixWord ++ tailWord_177907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_177924 : List Nat := [2, 3, 2, 2, 1, 2, 2, 4, 4]
def baseStart_177924 : Nat := 118140960795 + 177924 * 2 ^ 59
def prefixEnd_177924 : Nat := 4983230072969 + 3 ^ 40 * 177924 * 2
def baseEnd_177924 : Nat := 20302340437926023384833

theorem tailTrace_177924 : CollatzResearch.WordTrace tailWord_177924 prefixEnd_177924 20302340437926023384833 := by
  unfold tailWord_177924
  simp only [CollatzResearch.WordTrace]
  refine ⟨3244710703709604922538413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4326280938279473230051217 3244710703709604922538413)
  ·
    refine ⟨1216766513891101845951905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3244710703709604922538413 1216766513891101845951905)
    ·
      refine ⟨912574885418326384463929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1216766513891101845951905 912574885418326384463929)
      ·
        refine ⟨684431164063744788347947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 912574885418326384463929 684431164063744788347947)
        ·
          refine ⟨1026646746095617182521921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 684431164063744788347947 1026646746095617182521921)
          ·
            refine ⟨769985059571712886891441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1026646746095617182521921 769985059571712886891441)
            ·
              refine ⟨577488794678784665168581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 769985059571712886891441 577488794678784665168581)
              ·
                refine ⟨108279149002272124719109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 577488794678784665168581 108279149002272124719109)
                ·
                  refine ⟨20302340437926023384833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 108279149002272124719109 20302340437926023384833)
                  ·
                    rfl

theorem cell22_177924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 2, 4, 4].length) (baseStart_177924 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_177924 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_177924 prefixEnd_177924 := by exact prefixLift 177924
  have htrace : WordTrace (prefixWord ++ tailWord_177924) baseStart_177924 baseEnd_177924 := by
    simpa [prefixWord, tailWord_177924, baseEnd_177924] using wordTrace_append hprefix tailTrace_177924
  have hstable : (prefixWord ++ tailWord_177924).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_177924).length < 2 ^ (prefixWord ++ tailWord_177924).sum := by decide
  have hdescent : baseEnd_177924 < baseStart_177924 := by decide
  rcases family_descends (prefixWord ++ tailWord_177924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_177990 : List Nat := [6, 1, 1, 2, 1, 1, 4, 1, 2, 3]
def baseStart_177990 : Nat := 118140960795 + 177990 * 2 ^ 59
def prefixEnd_177990 : Nat := 4983230072969 + 3 ^ 40 * 177990 * 2
def baseEnd_177990 : Nat := 60929614462575898004297

theorem tailTrace_177990 : CollatzResearch.WordTrace tailWord_177990 prefixEnd_177990 60929614462575898004297 := by
  unfold tailWord_177990
  simp only [CollatzResearch.WordTrace]
  refine ⟨202869644536878222405607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 4327885750120068744652949 202869644536878222405607)
  ·
    refine ⟨304304466805317333608411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202869644536878222405607 304304466805317333608411)
    ·
      refine ⟨456456700207976000412617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 304304466805317333608411 456456700207976000412617)
      ·
        refine ⟨342342525155982000309463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 456456700207976000412617 342342525155982000309463)
        ·
          refine ⟨513513787733973000464195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 342342525155982000309463 513513787733973000464195)
          ·
            refine ⟨770270681600959500696293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 513513787733973000464195 770270681600959500696293)
            ·
              refine ⟨144425752800179906380555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 770270681600959500696293 144425752800179906380555)
              ·
                refine ⟨216638629200269859570833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 144425752800179906380555 216638629200269859570833)
                ·
                  refine ⟨162478971900202394678125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 216638629200269859570833 162478971900202394678125)
                  ·
                    refine ⟨60929614462575898004297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 162478971900202394678125 60929614462575898004297)
                    ·
                      rfl

theorem cell22_177990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 4, 1, 2, 3].length) (baseStart_177990 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_177990 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_177990 prefixEnd_177990 := by exact prefixLift 177990
  have htrace : WordTrace (prefixWord ++ tailWord_177990) baseStart_177990 baseEnd_177990 := by
    simpa [prefixWord, tailWord_177990, baseEnd_177990] using wordTrace_append hprefix tailTrace_177990
  have hstable : (prefixWord ++ tailWord_177990).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_177990).length < 2 ^ (prefixWord ++ tailWord_177990).sum := by decide
  have hdescent : baseEnd_177990 < baseStart_177990 := by decide
  rcases family_descends (prefixWord ++ tailWord_177990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178046 : List Nat := [4, 2, 3, 1, 1, 2, 1, 1, 2, 5]
def baseStart_178046 : Nat := 118140960795 + 178046 * 2 ^ 59
def prefixEnd_178046 : Nat := 4983230072969 + 3 ^ 40 * 178046 * 2
def baseEnd_178046 : Nat := 60948784407010418604125

theorem tailTrace_178046 : CollatzResearch.WordTrace tailWord_178046 prefixEnd_178046 60948784407010418604125 := by
  unfold tailWord_178046
  simp only [CollatzResearch.WordTrace]
  refine ⟨811733889122153085127249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4329247408651483120678661 811733889122153085127249)
  ·
    refine ⟨608800416841614813845437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 811733889122153085127249 608800416841614813845437)
    ·
      refine ⟨228300156315605555192039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 608800416841614813845437 228300156315605555192039)
      ·
        refine ⟨342450234473408332788059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 228300156315605555192039 342450234473408332788059)
        ·
          refine ⟨513675351710112499182089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 342450234473408332788059 513675351710112499182089)
          ·
            refine ⟨385256513782584374386567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 513675351710112499182089 385256513782584374386567)
            ·
              refine ⟨577884770673876561579851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 385256513782584374386567 577884770673876561579851)
              ·
                refine ⟨866827156010814842369777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 577884770673876561579851 866827156010814842369777)
                ·
                  refine ⟨650120367008111131777333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 866827156010814842369777 650120367008111131777333)
                  ·
                    refine ⟨60948784407010418604125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 650120367008111131777333 60948784407010418604125)
                    ·
                      rfl

theorem cell22_178046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 1, 1, 2, 5].length) (baseStart_178046 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_178046 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_178046 prefixEnd_178046 := by exact prefixLift 178046
  have htrace : WordTrace (prefixWord ++ tailWord_178046) baseStart_178046 baseEnd_178046 := by
    simpa [prefixWord, tailWord_178046, baseEnd_178046] using wordTrace_append hprefix tailTrace_178046
  have hstable : (prefixWord ++ tailWord_178046).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178046).length < 2 ^ (prefixWord ++ tailWord_178046).sum := by decide
  have hdescent : baseEnd_178046 < baseStart_178046 := by decide
  rcases family_descends (prefixWord ++ tailWord_178046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178074 : List Nat := [3, 1, 1, 4, 2, 1, 2, 2, 1, 5]
def baseStart_178074 : Nat := 118140960795 + 178074 * 2 ^ 59
def prefixEnd_178074 : Nat := 4983230072969 + 3 ^ 40 * 178074 * 2
def baseEnd_178074 : Nat := 60958369379227678904039

theorem tailTrace_178074 : CollatzResearch.WordTrace tailWord_178074 prefixEnd_178074 60958369379227678904039 := by
  unfold tailWord_178074
  simp only [CollatzResearch.WordTrace]
  refine ⟨1623723089218946365759319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4329928237917190308691517 1623723089218946365759319)
  ·
    refine ⟨2435584633828419548638979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1623723089218946365759319 2435584633828419548638979)
    ·
      refine ⟨3653376950742629322958469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2435584633828419548638979 3653376950742629322958469)
      ·
        refine ⟨685008178264242998054713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3653376950742629322958469 685008178264242998054713)
        ·
          refine ⟨513756133698182248541035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 685008178264242998054713 513756133698182248541035)
          ·
            refine ⟨770634200547273372811553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 513756133698182248541035 770634200547273372811553)
            ·
              refine ⟨577975650410455029608665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 770634200547273372811553 577975650410455029608665)
              ·
                refine ⟨433481737807841272206499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 577975650410455029608665 433481737807841272206499)
                ·
                  refine ⟨650222606711761908309749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 433481737807841272206499 650222606711761908309749)
                  ·
                    refine ⟨60958369379227678904039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 650222606711761908309749 60958369379227678904039)
                    ·
                      rfl

theorem cell22_178074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 2, 2, 1, 5].length) (baseStart_178074 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_178074 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_178074 prefixEnd_178074 := by exact prefixLift 178074
  have htrace : WordTrace (prefixWord ++ tailWord_178074) baseStart_178074 baseEnd_178074 := by
    simpa [prefixWord, tailWord_178074, baseEnd_178074] using wordTrace_append hprefix tailTrace_178074
  have hstable : (prefixWord ++ tailWord_178074).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178074).length < 2 ^ (prefixWord ++ tailWord_178074).sum := by decide
  have hdescent : baseEnd_178074 < baseStart_178074 := by decide
  rcases family_descends (prefixWord ++ tailWord_178074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178076 : List Nat := [2, 2, 3, 3, 1, 1, 1, 5, 4]
def baseStart_178076 : Nat := 118140960795 + 178076 * 2 ^ 59
def prefixEnd_178076 : Nat := 4983230072969 + 3 ^ 40 * 178076 * 2
def baseEnd_178076 : Nat := 20319684673366780118011

theorem tailTrace_178076 : CollatzResearch.WordTrace tailWord_178076 prefixEnd_178076 20319684673366780118011 := by
  unfold tailWord_178076
  simp only [CollatzResearch.WordTrace]
  refine ⟨3247482651434269902305041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4329976868579026536406721 3247482651434269902305041)
  ·
    refine ⟨2435611988575702426728781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3247482651434269902305041 2435611988575702426728781)
    ·
      refine ⟨913354495715888410023293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2435611988575702426728781 913354495715888410023293)
      ·
        refine ⟨342507935893458153758735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 913354495715888410023293 342507935893458153758735)
        ·
          refine ⟨513761903840187230638103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 342507935893458153758735 513761903840187230638103)
          ·
            refine ⟨770642855760280845957155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 513761903840187230638103 770642855760280845957155)
            ·
              refine ⟨1155964283640421268935733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 770642855760280845957155 1155964283640421268935733)
              ·
                refine ⟨108371651591289493962725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1155964283640421268935733 108371651591289493962725)
                ·
                  refine ⟨20319684673366780118011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 108371651591289493962725 20319684673366780118011)
                  ·
                    rfl

theorem cell22_178076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 5, 4].length) (baseStart_178076 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_178076 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_178076 prefixEnd_178076 := by exact prefixLift 178076
  have htrace : WordTrace (prefixWord ++ tailWord_178076) baseStart_178076 baseEnd_178076 := by
    simpa [prefixWord, tailWord_178076, baseEnd_178076] using wordTrace_append hprefix tailTrace_178076
  have hstable : (prefixWord ++ tailWord_178076).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178076).length < 2 ^ (prefixWord ++ tailWord_178076).sum := by decide
  have hdescent : baseEnd_178076 < baseStart_178076 := by decide
  rcases family_descends (prefixWord ++ tailWord_178076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178108 : List Nat := [2, 2, 2, 5, 1, 2, 1, 1, 1, 5]
def baseStart_178108 : Nat := 118140960795 + 178108 * 2 ^ 59
def prefixEnd_178108 : Nat := 4983230072969 + 3 ^ 40 * 178108 * 2
def baseEnd_178108 : Nat := 60970008274062923553935

theorem tailTrace_178108 : CollatzResearch.WordTrace tailWord_178108 prefixEnd_178108 60970008274062923553935 := by
  unfold tailWord_178108
  simp only [CollatzResearch.WordTrace]
  refine ⟨3248066219376304634887489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4330754959168406179849985 3248066219376304634887489)
  ·
    refine ⟨2436049664532228476165617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3248066219376304634887489 2436049664532228476165617)
    ·
      refine ⟨1827037248399171357124213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2436049664532228476165617 1827037248399171357124213)
      ·
        refine ⟨171284742037422314730395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1827037248399171357124213 171284742037422314730395)
        ·
          refine ⟨256927113056133472095593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171284742037422314730395 256927113056133472095593)
          ·
            refine ⟨192695334792100104071695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 256927113056133472095593 192695334792100104071695)
            ·
              refine ⟨289043002188150156107543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 192695334792100104071695 289043002188150156107543)
              ·
                refine ⟨433564503282225234161315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 289043002188150156107543 433564503282225234161315)
                ·
                  refine ⟨650346754923337851241973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 433564503282225234161315 650346754923337851241973)
                  ·
                    refine ⟨60970008274062923553935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 650346754923337851241973 60970008274062923553935)
                    ·
                      rfl

theorem cell22_178108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 1, 1, 1, 5].length) (baseStart_178108 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_178108 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_178108 prefixEnd_178108 := by exact prefixLift 178108
  have htrace : WordTrace (prefixWord ++ tailWord_178108) baseStart_178108 baseEnd_178108 := by
    simpa [prefixWord, tailWord_178108, baseEnd_178108] using wordTrace_append hprefix tailTrace_178108
  have hstable : (prefixWord ++ tailWord_178108).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178108).length < 2 ^ (prefixWord ++ tailWord_178108).sum := by decide
  have hdescent : baseEnd_178108 < baseStart_178108 := by decide
  rcases family_descends (prefixWord ++ tailWord_178108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178140 : List Nat := [2, 2, 6, 1, 1, 1, 1, 2, 2, 4]
def baseStart_178140 : Nat := 118140960795 + 178140 * 2 ^ 59
def prefixEnd_178140 : Nat := 4983230072969 + 3 ^ 40 * 178140 * 2
def baseEnd_178140 : Nat := 60980962528025506753837

theorem tailTrace_178140 : CollatzResearch.WordTrace tailWord_178140 prefixEnd_178140 60980962528025506753837 := by
  unfold tailWord_178140
  simp only [CollatzResearch.WordTrace]
  refine ⟨3248649787318339367469937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4331533049757785823293249 3248649787318339367469937)
  ·
    refine ⟨2436487340488754525602453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3248649787318339367469937 2436487340488754525602453)
    ·
      refine ⟨114210344085410368387615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 2436487340488754525602453 114210344085410368387615)
      ·
        refine ⟨171315516128115552581423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114210344085410368387615 171315516128115552581423)
        ·
          refine ⟨256973274192173328872135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171315516128115552581423 256973274192173328872135)
          ·
            refine ⟨385459911288259993308203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 256973274192173328872135 385459911288259993308203)
            ·
              refine ⟨578189866932389989962305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 385459911288259993308203 578189866932389989962305)
              ·
                refine ⟨433642400199292492471729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 578189866932389989962305 433642400199292492471729)
                ·
                  refine ⟨325231800149469369353797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 433642400199292492471729 325231800149469369353797)
                  ·
                    refine ⟨60980962528025506753837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 325231800149469369353797 60980962528025506753837)
                    ·
                      rfl

theorem cell22_178140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 1, 2, 2, 4].length) (baseStart_178140 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_178140 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_178140 prefixEnd_178140 := by exact prefixLift 178140
  have htrace : WordTrace (prefixWord ++ tailWord_178140) baseStart_178140 baseEnd_178140 := by
    simpa [prefixWord, tailWord_178140, baseEnd_178140] using wordTrace_append hprefix tailTrace_178140
  have hstable : (prefixWord ++ tailWord_178140).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178140).length < 2 ^ (prefixWord ++ tailWord_178140).sum := by decide
  have hdescent : baseEnd_178140 < baseStart_178140 := by decide
  rcases family_descends (prefixWord ++ tailWord_178140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178211 : List Nat := [1, 1, 1, 4, 3, 1, 3, 4, 4]
def baseStart_178211 : Nat := 118140960795 + 178211 * 2 ^ 59
def prefixEnd_178211 : Nat := 4983230072969 + 3 ^ 40 * 178211 * 2
def baseEnd_178211 : Nat := 20335089093001662742873

theorem tailTrace_178211 : CollatzResearch.WordTrace tailWord_178211 prefixEnd_178211 20335089093001662742873 := by
  unfold tailWord_178211
  simp only [CollatzResearch.WordTrace]
  refine ⟨6499889157379457860774487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4333259438252971907182991 6499889157379457860774487)
  ·
    refine ⟨9749833736069186791161731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6499889157379457860774487 9749833736069186791161731)
    ·
      refine ⟨14624750604103780186742597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9749833736069186791161731 14624750604103780186742597)
      ·
        refine ⟨2742140738269458785014237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14624750604103780186742597 2742140738269458785014237)
        ·
          refine ⟨1028302776851047044380339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2742140738269458785014237 1028302776851047044380339)
          ·
            refine ⟨1542454165276570566570509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1028302776851047044380339 1542454165276570566570509)
            ·
              refine ⟨578420311978713962463941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1542454165276570566570509 578420311978713962463941)
              ·
                refine ⟨108453808496008867961989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 578420311978713962463941 108453808496008867961989)
                ·
                  refine ⟨20335089093001662742873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 108453808496008867961989 20335089093001662742873)
                  ·
                    rfl

theorem cell22_178211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 3, 4, 4].length) (baseStart_178211 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_178211 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_178211 prefixEnd_178211 := by exact prefixLift 178211
  have htrace : WordTrace (prefixWord ++ tailWord_178211) baseStart_178211 baseEnd_178211 := by
    simpa [prefixWord, tailWord_178211, baseEnd_178211] using wordTrace_append hprefix tailTrace_178211
  have hstable : (prefixWord ++ tailWord_178211).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178211).length < 2 ^ (prefixWord ++ tailWord_178211).sum := by decide
  have hdescent : baseEnd_178211 < baseStart_178211 := by decide
  rcases family_descends (prefixWord ++ tailWord_178211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178226 : List Nat := [3, 2, 1, 1, 2, 4, 2, 1, 1, 5]
def baseStart_178226 : Nat := 118140960795 + 178226 * 2 ^ 59
def prefixEnd_178226 : Nat := 4983230072969 + 3 ^ 40 * 178226 * 2
def baseEnd_178226 : Nat := 61010402085549949103573

theorem tailTrace_178226 : CollatzResearch.WordTrace tailWord_178226 prefixEnd_178226 61010402085549949103573 := by
  unfold tailWord_178226
  simp only [CollatzResearch.WordTrace]
  refine ⟨1625109063081278855642633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4333624168216743615047021 1625109063081278855642633)
  ·
    refine ⟨1218831797310959141731975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1625109063081278855642633 1218831797310959141731975)
    ·
      refine ⟨1828247695966438712597963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1218831797310959141731975 1828247695966438712597963)
      ·
        refine ⟨2742371543949658068896945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1828247695966438712597963 2742371543949658068896945)
        ·
          refine ⟨2056778657962243551672709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2742371543949658068896945 2056778657962243551672709)
          ·
            refine ⟨385645998367920665938633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2056778657962243551672709 385645998367920665938633)
            ·
              refine ⟨289234498775940499453975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 385645998367920665938633 289234498775940499453975)
              ·
                refine ⟨433851748163910749180963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 289234498775940499453975 433851748163910749180963)
                ·
                  refine ⟨650777622245866123771445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 433851748163910749180963 650777622245866123771445)
                  ·
                    refine ⟨61010402085549949103573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 650777622245866123771445 61010402085549949103573)
                    ·
                      rfl

theorem cell22_178226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 2, 1, 1, 5].length) (baseStart_178226 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_178226 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_178226 prefixEnd_178226 := by exact prefixLift 178226
  have htrace : WordTrace (prefixWord ++ tailWord_178226) baseStart_178226 baseEnd_178226 := by
    simpa [prefixWord, tailWord_178226, baseEnd_178226] using wordTrace_append hprefix tailTrace_178226
  have hstable : (prefixWord ++ tailWord_178226).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178226).length < 2 ^ (prefixWord ++ tailWord_178226).sum := by decide
  have hdescent : baseEnd_178226 < baseStart_178226 := by decide
  rcases family_descends (prefixWord ++ tailWord_178226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178228 : List Nat := [2, 5, 1, 2, 2, 1, 1, 2, 6]
def baseStart_178228 : Nat := 118140960795 + 178228 * 2 ^ 59
def prefixEnd_178228 : Nat := 4983230072969 + 3 ^ 40 * 178228 * 2
def baseEnd_178228 : Nat := 20337028908807536851189

theorem tailTrace_178228 : CollatzResearch.WordTrace tailWord_178228 prefixEnd_178228 20337028908807536851189 := by
  unfold tailWord_178228
  simp only [CollatzResearch.WordTrace]
  refine ⟨3250254599158934882071669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4333672798878579842762225 3250254599158934882071669)
  ·
    refine ⟨304711368671150145194219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3250254599158934882071669 304711368671150145194219)
    ·
      refine ⟨457067053006725217791329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 304711368671150145194219 457067053006725217791329)
      ·
        refine ⟨342800289755043913343497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 457067053006725217791329 342800289755043913343497)
        ·
          refine ⟨257100217316282935007623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 342800289755043913343497 257100217316282935007623)
          ·
            refine ⟨385650325974424402511435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 257100217316282935007623 385650325974424402511435)
            ·
              refine ⟨578475488961636603767153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 385650325974424402511435 578475488961636603767153)
              ·
                refine ⟨433856616721227452825365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 578475488961636603767153 433856616721227452825365)
                ·
                  refine ⟨20337028908807536851189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 433856616721227452825365 20337028908807536851189)
                  ·
                    rfl

theorem cell22_178228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 1, 2, 6].length) (baseStart_178228 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_178228 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_178228 prefixEnd_178228 := by exact prefixLift 178228
  have htrace : WordTrace (prefixWord ++ tailWord_178228) baseStart_178228 baseEnd_178228 := by
    simpa [prefixWord, tailWord_178228, baseEnd_178228] using wordTrace_append hprefix tailTrace_178228
  have hstable : (prefixWord ++ tailWord_178228).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178228).length < 2 ^ (prefixWord ++ tailWord_178228).sum := by decide
  have hdescent : baseEnd_178228 < baseStart_178228 := by decide
  rcases family_descends (prefixWord ++ tailWord_178228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178241 : List Nat := [1, 2, 5, 1, 2, 2, 1, 1, 1, 6]
def baseStart_178241 : Nat := 118140960795 + 178241 * 2 ^ 59
def prefixEnd_178241 : Nat := 4983230072969 + 3 ^ 40 * 178241 * 2
def baseEnd_178241 : Nat := 61015536892094909978527

theorem tailTrace_178241 : CollatzResearch.WordTrace tailWord_178241 prefixEnd_178241 61015536892094909978527 := by
  unfold tailWord_178241
  simp only [CollatzResearch.WordTrace]
  refine ⟨6500983347270772984366577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4333988898180515322911051 6500983347270772984366577)
  ·
    refine ⟨4875737510453079738274933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6500983347270772984366577 4875737510453079738274933)
    ·
      refine ⟨457100391604976225463275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4875737510453079738274933 457100391604976225463275)
      ·
        refine ⟨685650587407464338194913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 457100391604976225463275 685650587407464338194913)
        ·
          refine ⟨514237940555598253646185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 685650587407464338194913 514237940555598253646185)
          ·
            refine ⟨385678455416698690234639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 514237940555598253646185 385678455416698690234639)
            ·
              refine ⟨578517683125048035351959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 385678455416698690234639 578517683125048035351959)
              ·
                refine ⟨867776524687572053027939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 578517683125048035351959 867776524687572053027939)
                ·
                  refine ⟨1301664787031358079541909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 867776524687572053027939 1301664787031358079541909)
                  ·
                    refine ⟨61015536892094909978527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1301664787031358079541909 61015536892094909978527)
                    ·
                      rfl

theorem cell22_178241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 1, 1, 1, 6].length) (baseStart_178241 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_178241 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_178241 prefixEnd_178241 := by exact prefixLift 178241
  have htrace : WordTrace (prefixWord ++ tailWord_178241) baseStart_178241 baseEnd_178241 := by
    simpa [prefixWord, tailWord_178241, baseEnd_178241] using wordTrace_append hprefix tailTrace_178241
  have hstable : (prefixWord ++ tailWord_178241).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178241).length < 2 ^ (prefixWord ++ tailWord_178241).sum := by decide
  have hdescent : baseEnd_178241 < baseStart_178241 := by decide
  rcases family_descends (prefixWord ++ tailWord_178241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178322 : List Nat := [3, 2, 3, 1, 1, 1, 5, 2, 1, 3]
def baseStart_178322 : Nat := 118140960795 + 178322 * 2 ^ 59
def prefixEnd_178322 : Nat := 4983230072969 + 3 ^ 40 * 178322 * 2
def baseEnd_178322 : Nat := 61043264847437698703279

theorem tailTrace_178322 : CollatzResearch.WordTrace tailWord_178322 prefixEnd_178322 61043264847437698703279 := by
  unfold tailWord_178322
  simp only [CollatzResearch.WordTrace]
  refine ⟨1625984414994330954516305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4335958439984882545376813 1625984414994330954516305)
  ·
    refine ⟨1219488311245748215887229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1625984414994330954516305 1219488311245748215887229)
    ·
      refine ⟨457308116717155580957711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1219488311245748215887229 457308116717155580957711)
      ·
        refine ⟨685962175075733371436567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 457308116717155580957711 685962175075733371436567)
        ·
          refine ⟨1028943262613600057154851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 685962175075733371436567 1028943262613600057154851)
          ·
            refine ⟨1543414893920400085732277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1028943262613600057154851 1543414893920400085732277)
            ·
              refine ⟨144695146305037508037401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1543414893920400085732277 144695146305037508037401)
              ·
                refine ⟨108521359728778131028051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 144695146305037508037401 108521359728778131028051)
                ·
                  refine ⟨162782039593167196542077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 108521359728778131028051 162782039593167196542077)
                  ·
                    refine ⟨61043264847437698703279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 162782039593167196542077 61043264847437698703279)
                    ·
                      rfl

theorem cell22_178322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 5, 2, 1, 3].length) (baseStart_178322 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_178322 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_178322 prefixEnd_178322 := by exact prefixLift 178322
  have htrace : WordTrace (prefixWord ++ tailWord_178322) baseStart_178322 baseEnd_178322 := by
    simpa [prefixWord, tailWord_178322, baseEnd_178322] using wordTrace_append hprefix tailTrace_178322
  have hstable : (prefixWord ++ tailWord_178322).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178322).length < 2 ^ (prefixWord ++ tailWord_178322).sum := by decide
  have hdescent : baseEnd_178322 < baseStart_178322 := by decide
  rcases family_descends (prefixWord ++ tailWord_178322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178335 : List Nat := [1, 1, 2, 6, 1, 3, 2, 1, 5]
def baseStart_178335 : Nat := 118140960795 + 178335 * 2 ^ 59
def prefixEnd_178335 : Nat := 4983230072969 + 3 ^ 40 * 178335 * 2
def baseEnd_178335 : Nat := 20349238337703332709413

theorem tailTrace_178335 : CollatzResearch.WordTrace tailWord_178335 prefixEnd_178335 20349238337703332709413 := by
  unfold tailWord_178335
  simp only [CollatzResearch.WordTrace]
  refine ⟨6504411808930227038288459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4336274539286818025525639 6504411808930227038288459)
  ·
    refine ⟨9756617713395340557432689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6504411808930227038288459 9756617713395340557432689)
    ·
      refine ⟨7317463285046505418074517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9756617713395340557432689 7317463285046505418074517)
      ·
        refine ⟨343006091486554941472243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 7317463285046505418074517 343006091486554941472243)
        ·
          refine ⟨514509137229832412208365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 343006091486554941472243 514509137229832412208365)
          ·
            refine ⟨192940926461187154578137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 514509137229832412208365 192940926461187154578137)
            ·
              refine ⟨144705694845890365933603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 192940926461187154578137 144705694845890365933603)
              ·
                refine ⟨217058542268835548900405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 144705694845890365933603 217058542268835548900405)
                ·
                  refine ⟨20349238337703332709413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 217058542268835548900405 20349238337703332709413)
                  ·
                    rfl

theorem cell22_178335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 2, 1, 5].length) (baseStart_178335 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_178335 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_178335 prefixEnd_178335 := by exact prefixLift 178335
  have htrace : WordTrace (prefixWord ++ tailWord_178335) baseStart_178335 baseEnd_178335 := by
    simpa [prefixWord, tailWord_178335, baseEnd_178335] using wordTrace_append hprefix tailTrace_178335
  have hstable : (prefixWord ++ tailWord_178335).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178335).length < 2 ^ (prefixWord ++ tailWord_178335).sum := by decide
  have hdescent : baseEnd_178335 < baseStart_178335 := by decide
  rcases family_descends (prefixWord ++ tailWord_178335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178361 : List Nat := [1, 2, 1, 4, 1, 2, 3, 2, 1, 5]
def baseStart_178361 : Nat := 118140960795 + 178361 * 2 ^ 59
def prefixEnd_178361 : Nat := 4983230072969 + 3 ^ 40 * 178361 * 2
def baseEnd_178361 : Nat := 61056615344454596978159

theorem tailTrace_178361 : CollatzResearch.WordTrace tailWord_178361 prefixEnd_178361 61056615344454596978159 := by
  unfold tailWord_178361
  simp only [CollatzResearch.WordTrace]
  refine ⟨6505360106836033478734937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4336906737890688985823291 6505360106836033478734937)
  ·
    refine ⟨4879020080127025109051203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6505360106836033478734937 4879020080127025109051203)
    ·
      refine ⟨7318530120190537663576805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4879020080127025109051203 7318530120190537663576805)
      ·
        refine ⟨1372224397535725811920651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7318530120190537663576805 1372224397535725811920651)
        ·
          refine ⟨2058336596303588717880977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1372224397535725811920651 2058336596303588717880977)
          ·
            refine ⟨1543752447227691538410733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2058336596303588717880977 1543752447227691538410733)
            ·
              refine ⟨578907167710384326904025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1543752447227691538410733 578907167710384326904025)
              ·
                refine ⟨434180375782788245178019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 578907167710384326904025 434180375782788245178019)
                ·
                  refine ⟨651270563674182367767029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 434180375782788245178019 651270563674182367767029)
                  ·
                    refine ⟨61056615344454596978159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 651270563674182367767029 61056615344454596978159)
                    ·
                      rfl

theorem cell22_178361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 3, 2, 1, 5].length) (baseStart_178361 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_178361 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_178361 prefixEnd_178361 := by exact prefixLift 178361
  have htrace : WordTrace (prefixWord ++ tailWord_178361) baseStart_178361 baseEnd_178361 := by
    simpa [prefixWord, tailWord_178361, baseEnd_178361] using wordTrace_append hprefix tailTrace_178361
  have hstable : (prefixWord ++ tailWord_178361).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178361).length < 2 ^ (prefixWord ++ tailWord_178361).sum := by decide
  have hdescent : baseEnd_178361 < baseStart_178361 := by decide
  rcases family_descends (prefixWord ++ tailWord_178361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178408 : List Nat := [2, 1, 4, 1, 2, 3, 3, 6]
def baseStart_178408 : Nat := 118140960795 + 178408 * 2 ^ 59
def prefixEnd_178408 : Nat := 4983230072969 + 3 ^ 40 * 178408 * 2
def baseEnd_178408 : Nat := 6785856044995793450335

theorem tailTrace_178408 : CollatzResearch.WordTrace tailWord_178408 prefixEnd_178408 6785856044995793450335 := by
  unfold tailWord_178408
  simp only [CollatzResearch.WordTrace]
  refine ⟨3253537168832880252847939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4338049558443840337130585 3253537168832880252847939)
  ·
    refine ⟨4880305753249320379271909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3253537168832880252847939 4880305753249320379271909)
    ·
      refine ⟨915057328734247571113483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4880305753249320379271909 915057328734247571113483)
      ·
        refine ⟨1372585993101371356670225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 915057328734247571113483 1372585993101371356670225)
        ·
          refine ⟨1029439494826028517502669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1372585993101371356670225 1029439494826028517502669)
          ·
            refine ⟨386039810559760694063501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1029439494826028517502669 386039810559760694063501)
            ·
              refine ⟨144764928959910260273813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 386039810559760694063501 144764928959910260273813)
              ·
                refine ⟨6785856044995793450335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 144764928959910260273813 6785856044995793450335)
                ·
                  rfl

theorem cell22_178408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 3, 6].length) (baseStart_178408 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_178408 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_178408 prefixEnd_178408 := by exact prefixLift 178408
  have htrace : WordTrace (prefixWord ++ tailWord_178408) baseStart_178408 baseEnd_178408 := by
    simpa [prefixWord, tailWord_178408, baseEnd_178408] using wordTrace_append hprefix tailTrace_178408
  have hstable : (prefixWord ++ tailWord_178408).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178408).length < 2 ^ (prefixWord ++ tailWord_178408).sum := by decide
  have hdescent : baseEnd_178408 < baseStart_178408 := by decide
  rcases family_descends (prefixWord ++ tailWord_178408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178440 : List Nat := [2, 1, 3, 2, 3, 2, 2, 1, 3, 3]
def baseStart_178440 : Nat := 118140960795 + 178440 * 2 ^ 59
def prefixEnd_178440 : Nat := 4983230072969 + 3 ^ 40 * 178440 * 2
def baseEnd_178440 : Nat := 61083658658924724252917

theorem tailTrace_178440 : CollatzResearch.WordTrace tailWord_178440 prefixEnd_178440 61083658658924724252917 := by
  unfold tailWord_178440
  simp only [CollatzResearch.WordTrace]
  refine ⟨3254120736774914985430387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4338827649033219980573849 3254120736774914985430387)
  ·
    refine ⟨4881181105162372478145581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3254120736774914985430387 4881181105162372478145581)
    ·
      refine ⟨1830442914435889679304593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4881181105162372478145581 1830442914435889679304593)
      ·
        refine ⟨1372832185826917259478445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1830442914435889679304593 1372832185826917259478445)
        ·
          refine ⟨514812069685093972304417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1372832185826917259478445 514812069685093972304417)
          ·
            refine ⟨386109052263820479228313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 514812069685093972304417 386109052263820479228313)
            ·
              refine ⟨289581789197865359421235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 386109052263820479228313 289581789197865359421235)
              ·
                refine ⟨434372683796798039131853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 289581789197865359421235 434372683796798039131853)
                ·
                  refine ⟨162889756423799264674445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 434372683796798039131853 162889756423799264674445)
                  ·
                    refine ⟨61083658658924724252917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 162889756423799264674445 61083658658924724252917)
                    ·
                      rfl

theorem cell22_178440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 2, 1, 3, 3].length) (baseStart_178440 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_178440 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_178440 prefixEnd_178440 := by exact prefixLift 178440
  have htrace : WordTrace (prefixWord ++ tailWord_178440) baseStart_178440 baseEnd_178440 := by
    simpa [prefixWord, tailWord_178440, baseEnd_178440] using wordTrace_append hprefix tailTrace_178440
  have hstable : (prefixWord ++ tailWord_178440).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178440).length < 2 ^ (prefixWord ++ tailWord_178440).sum := by decide
  have hdescent : baseEnd_178440 < baseStart_178440 := by decide
  rcases family_descends (prefixWord ++ tailWord_178440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178483 : List Nat := [1, 1, 1, 2, 5, 1, 1, 5, 1, 4]
def baseStart_178483 : Nat := 118140960795 + 178483 * 2 ^ 59
def prefixEnd_178483 : Nat := 4983230072969 + 3 ^ 40 * 178483 * 2
def baseEnd_178483 : Nat := 61098378437686945427785

theorem tailTrace_178483 : CollatzResearch.WordTrace tailWord_178483 prefixEnd_178483 61098378437686945427785 := by
  unfold tailWord_178483
  simp only [CollatzResearch.WordTrace]
  refine ⟨6509809812394048314676103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4339873208262698876450735 6509809812394048314676103)
  ·
    refine ⟨9764714718591072472014155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6509809812394048314676103 9764714718591072472014155)
    ·
      refine ⟨14647072077886608708021233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9764714718591072472014155 14647072077886608708021233)
      ·
        refine ⟨10985304058414956531015925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14647072077886608708021233 10985304058414956531015925)
        ·
          refine ⟨1029872255476402174782743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10985304058414956531015925 1029872255476402174782743)
          ·
            refine ⟨1544808383214603262174115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1029872255476402174782743 1544808383214603262174115)
            ·
              refine ⟨2317212574821904893261173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1544808383214603262174115 2317212574821904893261173)
              ·
                refine ⟨217238678889553583743235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2317212574821904893261173 217238678889553583743235)
                ·
                  refine ⟨325858018334330375614853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 217238678889553583743235 325858018334330375614853)
                  ·
                    refine ⟨61098378437686945427785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 325858018334330375614853 61098378437686945427785)
                    ·
                      rfl

theorem cell22_178483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 5, 1, 4].length) (baseStart_178483 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_178483 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_178483 prefixEnd_178483 := by exact prefixLift 178483
  have htrace : WordTrace (prefixWord ++ tailWord_178483) baseStart_178483 baseEnd_178483 := by
    simpa [prefixWord, tailWord_178483, baseEnd_178483] using wordTrace_append hprefix tailTrace_178483
  have hstable : (prefixWord ++ tailWord_178483).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178483).length < 2 ^ (prefixWord ++ tailWord_178483).sum := by decide
  have hdescent : baseEnd_178483 < baseStart_178483 := by decide
  rcases family_descends (prefixWord ++ tailWord_178483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178496 : List Nat := [2, 1, 1, 2, 2, 1, 2, 1, 5, 5]
def baseStart_178496 : Nat := 118140960795 + 178496 * 2 ^ 59
def prefixEnd_178496 : Nat := 4983230072969 + 3 ^ 40 * 178496 * 2
def baseEnd_178496 : Nat := 61102828603359244852745

theorem tailTrace_178496 : CollatzResearch.WordTrace tailWord_178496 prefixEnd_178496 61102828603359244852745 := by
  unfold tailWord_178496
  simp only [CollatzResearch.WordTrace]
  refine ⟨3255141980673475767449671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4340189307564634356599561 3255141980673475767449671)
  ·
    refine ⟨4882712971010213651174507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3255141980673475767449671 4882712971010213651174507)
    ·
      refine ⟨7324069456515320476761761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4882712971010213651174507 7324069456515320476761761)
      ·
        refine ⟨5493052092386490357571321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7324069456515320476761761 5493052092386490357571321)
        ·
          refine ⟨4119789069289867768178491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5493052092386490357571321 4119789069289867768178491)
          ·
            refine ⟨6179683603934801652267737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4119789069289867768178491 6179683603934801652267737)
            ·
              refine ⟨4634762702951101239200803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6179683603934801652267737 4634762702951101239200803)
              ·
                refine ⟨6952144054426651858801205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4634762702951101239200803 6952144054426651858801205)
                ·
                  refine ⟨651763505102498611762613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 6952144054426651858801205 651763505102498611762613)
                  ·
                    refine ⟨61102828603359244852745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 651763505102498611762613 61102828603359244852745)
                    ·
                      rfl

theorem cell22_178496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 5, 5].length) (baseStart_178496 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_178496 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_178496 prefixEnd_178496 := by exact prefixLift 178496
  have htrace : WordTrace (prefixWord ++ tailWord_178496) baseStart_178496 baseEnd_178496 := by
    simpa [prefixWord, tailWord_178496, baseEnd_178496] using wordTrace_append hprefix tailTrace_178496
  have hstable : (prefixWord ++ tailWord_178496).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178496).length < 2 ^ (prefixWord ++ tailWord_178496).sum := by decide
  have hdescent : baseEnd_178496 < baseStart_178496 := by decide
  rcases family_descends (prefixWord ++ tailWord_178496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178511 : List Nat := [1, 1, 2, 1, 1, 2, 1, 6, 1, 6]
def baseStart_178511 : Nat := 118140960795 + 178511 * 2 ^ 59
def prefixEnd_178511 : Nat := 4983230072969 + 3 ^ 40 * 178511 * 2
def baseEnd_178511 : Nat := 61107963409904205727699

theorem tailTrace_178511 : CollatzResearch.WordTrace tailWord_178511 prefixEnd_178511 61107963409904205727699 := by
  unfold tailWord_178511
  simp only [CollatzResearch.WordTrace]
  refine ⟨6510831056292609096695387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4340554037528406064463591 6510831056292609096695387)
  ·
    refine ⟨9766246584438913645043081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6510831056292609096695387 9766246584438913645043081)
    ·
      refine ⟨7324684938329185233782311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9766246584438913645043081 7324684938329185233782311)
      ·
        refine ⟨10987027407493777850673467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7324684938329185233782311 10987027407493777850673467)
        ·
          refine ⟨16480541111240666776010201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10987027407493777850673467 16480541111240666776010201)
          ·
            refine ⟨12360405833430500082007651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16480541111240666776010201 12360405833430500082007651)
            ·
              refine ⟨18540608750145750123011477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12360405833430500082007651 18540608750145750123011477)
              ·
                refine ⟨869091035163082037016163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 18540608750145750123011477 869091035163082037016163)
                ·
                  refine ⟨1303636552744623055524245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 869091035163082037016163 1303636552744623055524245)
                  ·
                    refine ⟨61107963409904205727699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1303636552744623055524245 61107963409904205727699)
                    ·
                      rfl

theorem cell22_178511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 6, 1, 6].length) (baseStart_178511 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_178511 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_178511 prefixEnd_178511 := by exact prefixLift 178511
  have htrace : WordTrace (prefixWord ++ tailWord_178511) baseStart_178511 baseEnd_178511 := by
    simpa [prefixWord, tailWord_178511, baseEnd_178511] using wordTrace_append hprefix tailTrace_178511
  have hstable : (prefixWord ++ tailWord_178511).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178511).length < 2 ^ (prefixWord ++ tailWord_178511).sum := by decide
  have hdescent : baseEnd_178511 < baseStart_178511 := by decide
  rcases family_descends (prefixWord ++ tailWord_178511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178517 : List Nat := [1, 3, 2, 2, 4, 2, 1, 2, 1, 4]
def baseStart_178517 : Nat := 118140960795 + 178517 * 2 ^ 59
def prefixEnd_178517 : Nat := 4983230072969 + 3 ^ 40 * 178517 * 2
def baseEnd_178517 : Nat := 61110017332522190077681

theorem tailTrace_178517 : CollatzResearch.WordTrace tailWord_178517 prefixEnd_178517 61110017332522190077681 := by
  unfold tailWord_178517
  simp only [CollatzResearch.WordTrace]
  refine ⟨6511049894270872121413805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4340699929513914747609203 6511049894270872121413805)
  ·
    refine ⟨2441643710351577045530177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6511049894270872121413805 2441643710351577045530177)
    ·
      refine ⟨1831232782763682784147633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2441643710351577045530177 1831232782763682784147633)
      ·
        refine ⟨1373424587072762088110725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1831232782763682784147633 1373424587072762088110725)
        ·
          refine ⟨257517110076142891520761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1373424587072762088110725 257517110076142891520761)
          ·
            refine ⟨193137832557107168640571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 257517110076142891520761 193137832557107168640571)
            ·
              refine ⟨289706748835660752960857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 193137832557107168640571 289706748835660752960857)
              ·
                refine ⟨217280061626745564720643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 289706748835660752960857 217280061626745564720643)
                ·
                  refine ⟨325920092440118347080965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 217280061626745564720643 325920092440118347080965)
                  ·
                    refine ⟨61110017332522190077681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 325920092440118347080965 61110017332522190077681)
                    ·
                      rfl

theorem cell22_178517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 1, 2, 1, 4].length) (baseStart_178517 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_178517 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_178517 prefixEnd_178517 := by exact prefixLift 178517
  have htrace : WordTrace (prefixWord ++ tailWord_178517) baseStart_178517 baseEnd_178517 := by
    simpa [prefixWord, tailWord_178517, baseEnd_178517] using wordTrace_append hprefix tailTrace_178517
  have hstable : (prefixWord ++ tailWord_178517).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178517).length < 2 ^ (prefixWord ++ tailWord_178517).sum := by decide
  have hdescent : baseEnd_178517 < baseStart_178517 := by decide
  rcases family_descends (prefixWord ++ tailWord_178517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178530 : List Nat := [3, 3, 2, 1, 1, 3, 1, 2, 1, 5]
def baseStart_178530 : Nat := 118140960795 + 178530 * 2 ^ 59
def prefixEnd_178530 : Nat := 4983230072969 + 3 ^ 40 * 178530 * 2
def baseEnd_178530 : Nat := 61114467498194489502641

theorem tailTrace_178530 : CollatzResearch.WordTrace tailWord_178530 prefixEnd_178530 61114467498194489502641 := by
  unfold tailWord_178530
  simp only [CollatzResearch.WordTrace]
  refine ⟨1627881010805943835409261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4341016028815850227758029 1627881010805943835409261)
  ·
    refine ⟨610455379052228938278473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1627881010805943835409261 610455379052228938278473)
    ·
      refine ⟨457841534289171703708855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 610455379052228938278473 457841534289171703708855)
      ·
        refine ⟨686762301433757555563283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 457841534289171703708855 686762301433757555563283)
        ·
          refine ⟨1030143452150636333344925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 686762301433757555563283 1030143452150636333344925)
          ·
            refine ⟨386303794556488625004347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1030143452150636333344925 386303794556488625004347)
            ·
              refine ⟨579455691834732937506521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 386303794556488625004347 579455691834732937506521)
              ·
                refine ⟨434591768876049703129891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 579455691834732937506521 434591768876049703129891)
                ·
                  refine ⟨651887653314074554694837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 434591768876049703129891 651887653314074554694837)
                  ·
                    refine ⟨61114467498194489502641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 651887653314074554694837 61114467498194489502641)
                    ·
                      rfl

theorem cell22_178530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 1, 2, 1, 5].length) (baseStart_178530 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_178530 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_178530 prefixEnd_178530 := by exact prefixLift 178530
  have htrace : WordTrace (prefixWord ++ tailWord_178530) baseStart_178530 baseEnd_178530 := by
    simpa [prefixWord, tailWord_178530, baseEnd_178530] using wordTrace_append hprefix tailTrace_178530
  have hstable : (prefixWord ++ tailWord_178530).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178530).length < 2 ^ (prefixWord ++ tailWord_178530).sum := by decide
  have hdescent : baseEnd_178530 < baseStart_178530 := by decide
  rcases family_descends (prefixWord ++ tailWord_178530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178549 : List Nat := [1, 3, 4, 1, 2, 3, 2, 2, 4]
def baseStart_178549 : Nat := 118140960795 + 178549 * 2 ^ 59
def prefixEnd_178549 : Nat := 4983230072969 + 3 ^ 40 * 178549 * 2
def baseEnd_178549 : Nat := 20373657195494924425861

theorem tailTrace_178549 : CollatzResearch.WordTrace tailWord_178549 prefixEnd_178549 20373657195494924425861 := by
  unfold tailWord_178549
  simp only [CollatzResearch.WordTrace]
  refine ⟨6512217030154941586578701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4341478020103294391052467 6512217030154941586578701)
  ·
    refine ⟨2442081386308103094967013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6512217030154941586578701 2442081386308103094967013)
    ·
      refine ⟨457890259932769330306315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2442081386308103094967013 457890259932769330306315)
      ·
        refine ⟨686835389899153995459473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 457890259932769330306315 686835389899153995459473)
        ·
          refine ⟨515126542424365496594605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 686835389899153995459473 515126542424365496594605)
          ·
            refine ⟨193172453409137061222977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 515126542424365496594605 193172453409137061222977)
            ·
              refine ⟨144879340056852795917233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 193172453409137061222977 144879340056852795917233)
              ·
                refine ⟨108659505042639596937925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 144879340056852795917233 108659505042639596937925)
                ·
                  refine ⟨20373657195494924425861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 108659505042639596937925 20373657195494924425861)
                  ·
                    rfl

theorem cell22_178549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 2, 2, 4].length) (baseStart_178549 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_178549 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_178549 prefixEnd_178549 := by exact prefixLift 178549
  have htrace : WordTrace (prefixWord ++ tailWord_178549) baseStart_178549 baseEnd_178549 := by
    simpa [prefixWord, tailWord_178549, baseEnd_178549] using wordTrace_append hprefix tailTrace_178549
  have hstable : (prefixWord ++ tailWord_178549).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178549).length < 2 ^ (prefixWord ++ tailWord_178549).sum := by decide
  have hdescent : baseEnd_178549 < baseStart_178549 := by decide
  rcases family_descends (prefixWord ++ tailWord_178549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178592 : List Nat := [2, 1, 1, 4, 1, 3, 1, 5, 1, 3]
def baseStart_178592 : Nat := 118140960795 + 178592 * 2 ^ 59
def prefixEnd_178592 : Nat := 4983230072969 + 3 ^ 40 * 178592 * 2
def baseEnd_178592 : Nat := 61135691365246994452451

theorem tailTrace_178592 : CollatzResearch.WordTrace tailWord_178592 prefixEnd_178592 61135691365246994452451 := by
  unfold tailWord_178592
  simp only [CollatzResearch.WordTrace]
  refine ⟨3256892684499579965197015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4342523579332773286929353 3256892684499579965197015)
  ·
    refine ⟨4885339026749369947795523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3256892684499579965197015 4885339026749369947795523)
    ·
      refine ⟨7328008540124054921693285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4885339026749369947795523 7328008540124054921693285)
      ·
        refine ⟨1374001601273260297817491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7328008540124054921693285 1374001601273260297817491)
        ·
          refine ⟨2061002401909890446726237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1374001601273260297817491 2061002401909890446726237)
          ·
            refine ⟨772875900716208917522339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2061002401909890446726237 772875900716208917522339)
            ·
              refine ⟨1159313851074313376283509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 772875900716208917522339 1159313851074313376283509)
              ·
                refine ⟨108685673538216879026579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1159313851074313376283509 108685673538216879026579)
                ·
                  refine ⟨163028510307325318539869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 108685673538216879026579 163028510307325318539869)
                  ·
                    refine ⟨61135691365246994452451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 163028510307325318539869 61135691365246994452451)
                    ·
                      rfl

theorem cell22_178592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 5, 1, 3].length) (baseStart_178592 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_178592 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_178592 prefixEnd_178592 := by exact prefixLift 178592
  have htrace : WordTrace (prefixWord ++ tailWord_178592) baseStart_178592 baseEnd_178592 := by
    simpa [prefixWord, tailWord_178592, baseEnd_178592] using wordTrace_append hprefix tailTrace_178592
  have hstable : (prefixWord ++ tailWord_178592).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178592).length < 2 ^ (prefixWord ++ tailWord_178592).sum := by decide
  have hdescent : baseEnd_178592 < baseStart_178592 := by decide
  rcases family_descends (prefixWord ++ tailWord_178592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178618 : List Nat := [3, 1, 1, 1, 2, 1, 1, 3, 5, 4]
def baseStart_178618 : Nat := 118140960795 + 178618 * 2 ^ 59
def prefixEnd_178618 : Nat := 4983230072969 + 3 ^ 40 * 178618 * 2
def baseEnd_178618 : Nat := 61144591696591593302371

theorem tailTrace_178618 : CollatzResearch.WordTrace tailWord_178618 prefixEnd_178618 61144591696591593302371 := by
  unfold tailWord_178618
  simp only [CollatzResearch.WordTrace]
  refine ⟨1628683416726241592710127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4343155777936644247227005 1628683416726241592710127)
  ·
    refine ⟨2443025125089362389065191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1628683416726241592710127 2443025125089362389065191)
    ·
      refine ⟨3664537687634043583597787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2443025125089362389065191 3664537687634043583597787)
      ·
        refine ⟨5496806531451065375396681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3664537687634043583597787 5496806531451065375396681)
        ·
          refine ⟨4122604898588299031547511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5496806531451065375396681 4122604898588299031547511)
          ·
            refine ⟨6183907347882448547321267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4122604898588299031547511 6183907347882448547321267)
            ·
              refine ⟨9275861021823672820981901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6183907347882448547321267 9275861021823672820981901)
              ·
                refine ⟨3478447883183877307868213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9275861021823672820981901 3478447883183877307868213)
                ·
                  refine ⟨326104489048488497612645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3478447883183877307868213 326104489048488497612645)
                  ·
                    refine ⟨61144591696591593302371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 326104489048488497612645 61144591696591593302371)
                    ·
                      rfl

theorem cell22_178618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 3, 5, 4].length) (baseStart_178618 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_178618 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_178618 prefixEnd_178618 := by exact prefixLift 178618
  have htrace : WordTrace (prefixWord ++ tailWord_178618) baseStart_178618 baseEnd_178618 := by
    simpa [prefixWord, tailWord_178618, baseEnd_178618] using wordTrace_append hprefix tailTrace_178618
  have hstable : (prefixWord ++ tailWord_178618).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178618).length < 2 ^ (prefixWord ++ tailWord_178618).sum := by decide
  have hdescent : baseEnd_178618 < baseStart_178618 := by decide
  rcases family_descends (prefixWord ++ tailWord_178618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178620 : List Nat := [2, 2, 2, 4, 1, 1, 2, 1, 2, 5]
def baseStart_178620 : Nat := 118140960795 + 178620 * 2 ^ 59
def prefixEnd_178620 : Nat := 4983230072969 + 3 ^ 40 * 178620 * 2
def baseEnd_178620 : Nat := 61145276337464254752365

theorem tailTrace_178620 : CollatzResearch.WordTrace tailWord_178620 prefixEnd_178620 61145276337464254752365 := by
  unfold tailWord_178620
  simp only [CollatzResearch.WordTrace]
  refine ⟨3257403306448860356206657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4343204408598480474942209 3257403306448860356206657)
  ·
    refine ⟨2443052479836645267154993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3257403306448860356206657 2443052479836645267154993)
    ·
      refine ⟨1832289359877483950366245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2443052479836645267154993 1832289359877483950366245)
      ·
        refine ⟨343554254977028240693671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1832289359877483950366245 343554254977028240693671)
        ·
          refine ⟨515331382465542361040507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 343554254977028240693671 515331382465542361040507)
          ·
            refine ⟨772997073698313541560761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 515331382465542361040507 772997073698313541560761)
            ·
              refine ⟨579747805273735156170571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 772997073698313541560761 579747805273735156170571)
              ·
                refine ⟨869621707910602734255857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 579747805273735156170571 869621707910602734255857)
                ·
                  refine ⟨652216280932952050691893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 869621707910602734255857 652216280932952050691893)
                  ·
                    refine ⟨61145276337464254752365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 652216280932952050691893 61145276337464254752365)
                    ·
                      rfl

theorem cell22_178620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 2, 1, 2, 5].length) (baseStart_178620 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_178620 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_178620 prefixEnd_178620 := by exact prefixLift 178620
  have htrace : WordTrace (prefixWord ++ tailWord_178620) baseStart_178620 baseEnd_178620 := by
    simpa [prefixWord, tailWord_178620, baseEnd_178620] using wordTrace_append hprefix tailTrace_178620
  have hstable : (prefixWord ++ tailWord_178620).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178620).length < 2 ^ (prefixWord ++ tailWord_178620).sum := by decide
  have hdescent : baseEnd_178620 < baseStart_178620 := by decide
  rcases family_descends (prefixWord ++ tailWord_178620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178633 : List Nat := [1, 2, 1, 1, 2, 1, 6, 2, 6]
def baseStart_178633 : Nat := 118140960795 + 178633 * 2 ^ 59
def prefixEnd_178633 : Nat := 4983230072969 + 3 ^ 40 * 178633 * 2
def baseEnd_178633 : Nat := 20383242167712184725775

theorem tailTrace_178633 : CollatzResearch.WordTrace tailWord_178633 prefixEnd_178633 20383242167712184725775 := by
  unfold tailWord_178633
  simp only [CollatzResearch.WordTrace]
  refine ⟨6515280761850623932636553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4343520507900415955091035 6515280761850623932636553)
  ·
    refine ⟨4886460571387967949477415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6515280761850623932636553 4886460571387967949477415)
    ·
      refine ⟨7329690857081951924216123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4886460571387967949477415 7329690857081951924216123)
      ·
        refine ⟨10994536285622927886324185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7329690857081951924216123 10994536285622927886324185)
        ·
          refine ⟨8245902214217195914743139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10994536285622927886324185 8245902214217195914743139)
          ·
            refine ⟨12368853321325793872114709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8245902214217195914743139 12368853321325793872114709)
            ·
              refine ⟨579789999437146587755377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 12368853321325793872114709 579789999437146587755377)
              ·
                refine ⟨434842499577859940816533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 579789999437146587755377 434842499577859940816533)
                ·
                  refine ⟨20383242167712184725775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 434842499577859940816533 20383242167712184725775)
                  ·
                    rfl

theorem cell22_178633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 6, 2, 6].length) (baseStart_178633 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_178633 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_178633 prefixEnd_178633 := by exact prefixLift 178633
  have htrace : WordTrace (prefixWord ++ tailWord_178633) baseStart_178633 baseEnd_178633 := by
    simpa [prefixWord, tailWord_178633, baseEnd_178633] using wordTrace_append hprefix tailTrace_178633
  have hstable : (prefixWord ++ tailWord_178633).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178633).length < 2 ^ (prefixWord ++ tailWord_178633).sum := by decide
  have hdescent : baseEnd_178633 < baseStart_178633 := by decide
  rcases family_descends (prefixWord ++ tailWord_178633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178648 : List Nat := [2, 1, 2, 2, 2, 1, 1, 3, 3, 5]
def baseStart_178648 : Nat := 118140960795 + 178648 * 2 ^ 59
def prefixEnd_178648 : Nat := 4983230072969 + 3 ^ 40 * 178648 * 2
def baseEnd_178648 : Nat := 61154861309681515052279

theorem tailTrace_178648 : CollatzResearch.WordTrace tailWord_178648 prefixEnd_178648 61154861309681515052279 := by
  unfold tailWord_178648
  simp only [CollatzResearch.WordTrace]
  refine ⟨3257913928398140747216299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4343885237864187662955065 3257913928398140747216299)
  ·
    refine ⟨4886870892597211120824449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3257913928398140747216299 4886870892597211120824449)
    ·
      refine ⟨3665153169447908340618337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4886870892597211120824449 3665153169447908340618337)
      ·
        refine ⟨2748864877085931255463753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3665153169447908340618337 2748864877085931255463753)
        ·
          refine ⟨2061648657814448441597815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2748864877085931255463753 2061648657814448441597815)
          ·
            refine ⟨3092472986721672662396723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2061648657814448441597815 3092472986721672662396723)
            ·
              refine ⟨4638709480082508993595085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3092472986721672662396723 4638709480082508993595085)
              ·
                refine ⟨1739516055030940872598157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4638709480082508993595085 1739516055030940872598157)
                ·
                  refine ⟨652318520636602827224309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1739516055030940872598157 652318520636602827224309)
                  ·
                    refine ⟨61154861309681515052279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 652318520636602827224309 61154861309681515052279)
                    ·
                      rfl

theorem cell22_178648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 3, 3, 5].length) (baseStart_178648 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_178648 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_178648 prefixEnd_178648 := by exact prefixLift 178648
  have htrace : WordTrace (prefixWord ++ tailWord_178648) baseStart_178648 baseEnd_178648 := by
    simpa [prefixWord, tailWord_178648, baseEnd_178648] using wordTrace_append hprefix tailTrace_178648
  have hstable : (prefixWord ++ tailWord_178648).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178648).length < 2 ^ (prefixWord ++ tailWord_178648).sum := by decide
  have hdescent : baseEnd_178648 < baseStart_178648 := by decide
  rcases family_descends (prefixWord ++ tailWord_178648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178667 : List Nat := [1, 1, 1, 1, 2, 3, 7, 2, 4]
def baseStart_178667 : Nat := 118140960795 + 178667 * 2 ^ 59
def prefixEnd_178667 : Nat := 4983230072969 + 3 ^ 40 * 178667 * 2
def baseEnd_178667 : Nat := 20387121799323932942407

theorem tailTrace_178667 : CollatzResearch.WordTrace tailWord_178667 prefixEnd_178667 20387121799323932942407 := by
  unfold tailWord_178667
  simp only [CollatzResearch.WordTrace]
  refine ⟨6516520843727447739374255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4344347229151631826249503 6516520843727447739374255)
  ·
    refine ⟨9774781265591171609061383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6516520843727447739374255 9774781265591171609061383)
    ·
      refine ⟨14662171898386757413592075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9774781265591171609061383 14662171898386757413592075)
      ·
        refine ⟨21993257847580136120388113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14662171898386757413592075 21993257847580136120388113)
        ·
          refine ⟨16494943385685102090291085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21993257847580136120388113 16494943385685102090291085)
          ·
            refine ⟨6185603769631913283859157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16494943385685102090291085 6185603769631913283859157)
            ·
              refine ⟨144975088350747967590449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 6185603769631913283859157 144975088350747967590449)
              ·
                refine ⟨108731316263060975692837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 144975088350747967590449 108731316263060975692837)
                ·
                  refine ⟨20387121799323932942407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 108731316263060975692837 20387121799323932942407)
                  ·
                    rfl

theorem cell22_178667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 7, 2, 4].length) (baseStart_178667 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_178667 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_178667 prefixEnd_178667 := by exact prefixLift 178667
  have htrace : WordTrace (prefixWord ++ tailWord_178667) baseStart_178667 baseEnd_178667 := by
    simpa [prefixWord, tailWord_178667, baseEnd_178667] using wordTrace_append hprefix tailTrace_178667
  have hstable : (prefixWord ++ tailWord_178667).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178667).length < 2 ^ (prefixWord ++ tailWord_178667).sum := by decide
  have hdescent : baseEnd_178667 < baseStart_178667 := by decide
  rcases family_descends (prefixWord ++ tailWord_178667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178693 : List Nat := [1, 3, 1, 1, 2, 2, 2, 1, 2, 7]
def baseStart_178693 : Nat := 118140960795 + 178693 * 2 ^ 59
def prefixEnd_178693 : Nat := 4983230072969 + 3 ^ 40 * 178693 * 2
def baseEnd_178693 : Nat := 61170265729316397677141

theorem tailTrace_178693 : CollatzResearch.WordTrace tailWord_178693 prefixEnd_178693 61170265729316397677141 := by
  unfold tailWord_178693
  simp only [CollatzResearch.WordTrace]
  refine ⟨6517469141633254179820733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4344979427755502786547155 6517469141633254179820733)
  ·
    refine ⟨2444050928112470317432775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6517469141633254179820733 2444050928112470317432775)
    ·
      refine ⟨3666076392168705476149163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2444050928112470317432775 3666076392168705476149163)
      ·
        refine ⟨5499114588253058214223745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3666076392168705476149163 5499114588253058214223745)
        ·
          refine ⟨4124335941189793660667809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5499114588253058214223745 4124335941189793660667809)
          ·
            refine ⟨3093251955892345245500857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4124335941189793660667809 3093251955892345245500857)
            ·
              refine ⟨2319938966919258934125643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3093251955892345245500857 2319938966919258934125643)
              ·
                refine ⟨3479908450378888401188465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2319938966919258934125643 3479908450378888401188465)
                ·
                  refine ⟨2609931337784166300891349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3479908450378888401188465 2609931337784166300891349)
                  ·
                    refine ⟨61170265729316397677141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2609931337784166300891349 61170265729316397677141)
                    ·
                      rfl

theorem cell22_178693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 1, 2, 7].length) (baseStart_178693 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_178693 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_178693 prefixEnd_178693 := by exact prefixLift 178693
  have htrace : WordTrace (prefixWord ++ tailWord_178693) baseStart_178693 baseEnd_178693 := by
    simpa [prefixWord, tailWord_178693, baseEnd_178693] using wordTrace_append hprefix tailTrace_178693
  have hstable : (prefixWord ++ tailWord_178693).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178693).length < 2 ^ (prefixWord ++ tailWord_178693).sum := by decide
  have hdescent : baseEnd_178693 < baseStart_178693 := by decide
  rcases family_descends (prefixWord ++ tailWord_178693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178785 : List Nat := [1, 2, 3, 1, 1, 4, 1, 3, 6]
def baseStart_178785 : Nat := 118140960795 + 178785 * 2 ^ 59
def prefixEnd_178785 : Nat := 4983230072969 + 3 ^ 40 * 178785 * 2
def baseEnd_178785 : Nat := 20400586403152941458953

theorem tailTrace_178785 : CollatzResearch.WordTrace tailWord_178785 prefixEnd_178785 20400586403152941458953 := by
  unfold tailWord_178785
  simp only [CollatzResearch.WordTrace]
  refine ⟨6520824657299953892169809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4347216438199969261446539 6520824657299953892169809)
  ·
    refine ⟨4890618492974965419127357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6520824657299953892169809 4890618492974965419127357)
    ·
      refine ⟨1833981934865612032172759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4890618492974965419127357 1833981934865612032172759)
      ·
        refine ⟨2750972902298418048259139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1833981934865612032172759 2750972902298418048259139)
        ·
          refine ⟨4126459353447627072388709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2750972902298418048259139 4126459353447627072388709)
          ·
            refine ⟨773711128771430076072883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4126459353447627072388709 773711128771430076072883)
            ·
              refine ⟨1160566693157145114109325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 773711128771430076072883 1160566693157145114109325)
              ·
                refine ⟨435212509933929417790997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1160566693157145114109325 435212509933929417790997)
                ·
                  refine ⟨20400586403152941458953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 435212509933929417790997 20400586403152941458953)
                  ·
                    rfl

theorem cell22_178785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 3, 6].length) (baseStart_178785 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_178785 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_178785 prefixEnd_178785 := by exact prefixLift 178785
  have htrace : WordTrace (prefixWord ++ tailWord_178785) baseStart_178785 baseEnd_178785 := by
    simpa [prefixWord, tailWord_178785, baseEnd_178785] using wordTrace_append hprefix tailTrace_178785
  have hstable : (prefixWord ++ tailWord_178785).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178785).length < 2 ^ (prefixWord ++ tailWord_178785).sum := by decide
  have hdescent : baseEnd_178785 < baseStart_178785 := by decide
  rcases family_descends (prefixWord ++ tailWord_178785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178817 : List Nat := [1, 2, 4, 2, 1, 1, 1, 1, 6, 3]
def baseStart_178817 : Nat := 118140960795 + 178817 * 2 ^ 59
def prefixEnd_178817 : Nat := 4983230072969 + 3 ^ 40 * 178817 * 2
def baseEnd_178817 : Nat := 61212713463421407576761

theorem tailTrace_178817 : CollatzResearch.WordTrace tailWord_178817 prefixEnd_178817 61212713463421407576761 := by
  unfold tailWord_178817
  simp only [CollatzResearch.WordTrace]
  refine ⟨6521991793184023357334705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4347994528789348904889803 6521991793184023357334705)
  ·
    refine ⟨4891493844888017518001029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6521991793184023357334705 4891493844888017518001029)
    ·
      refine ⟨917155095916503284625193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4891493844888017518001029 917155095916503284625193)
      ·
        refine ⟨687866321937377463468895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 917155095916503284625193 687866321937377463468895)
        ·
          refine ⟨1031799482906066195203343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 687866321937377463468895 1031799482906066195203343)
          ·
            refine ⟨1547699224359099292805015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1031799482906066195203343 1547699224359099292805015)
            ·
              refine ⟨2321548836538648939207523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1547699224359099292805015 2321548836538648939207523)
              ·
                refine ⟨3482323254807973408811285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2321548836538648939207523 3482323254807973408811285)
                ·
                  refine ⟨163233902569123753538029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3482323254807973408811285 163233902569123753538029)
                  ·
                    refine ⟨61212713463421407576761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 163233902569123753538029 61212713463421407576761)
                    ·
                      rfl

theorem cell22_178817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 1, 6, 3].length) (baseStart_178817 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_178817 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_178817 prefixEnd_178817 := by exact prefixLift 178817
  have htrace : WordTrace (prefixWord ++ tailWord_178817) baseStart_178817 baseEnd_178817 := by
    simpa [prefixWord, tailWord_178817, baseEnd_178817] using wordTrace_append hprefix tailTrace_178817
  have hstable : (prefixWord ++ tailWord_178817).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178817).length < 2 ^ (prefixWord ++ tailWord_178817).sum := by decide
  have hdescent : baseEnd_178817 < baseStart_178817 := by decide
  rcases family_descends (prefixWord ++ tailWord_178817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178834 : List Nat := [3, 2, 3, 1, 2, 1, 2, 1, 4, 3]
def baseStart_178834 : Nat := 118140960795 + 178834 * 2 ^ 59
def prefixEnd_178834 : Nat := 4983230072969 + 3 ^ 40 * 178834 * 2
def baseEnd_178834 : Nat := 61218532910839029901709

theorem tailTrace_178834 : CollatzResearch.WordTrace tailWord_178834 prefixEnd_178834 61218532910839029901709 := by
  unfold tailWord_178834
  simp only [CollatzResearch.WordTrace]
  refine ⟨1630652958530608815175889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4348407889414956840469037 1630652958530608815175889)
  ·
    refine ⟨1222989718897956611381917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1630652958530608815175889 1222989718897956611381917)
    ·
      refine ⟨458621144586733729268219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1222989718897956611381917 458621144586733729268219)
      ·
        refine ⟨687931716880100593902329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 458621144586733729268219 687931716880100593902329)
        ·
          refine ⟨515948787660075445426747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 687931716880100593902329 515948787660075445426747)
          ·
            refine ⟨773923181490113168140121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 515948787660075445426747 773923181490113168140121)
            ·
              refine ⟨580442386117584876105091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 773923181490113168140121 580442386117584876105091)
              ·
                refine ⟨870663579176377314157637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 580442386117584876105091 870663579176377314157637)
                ·
                  refine ⟨163249421095570746404557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 870663579176377314157637 163249421095570746404557)
                  ·
                    refine ⟨61218532910839029901709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 163249421095570746404557 61218532910839029901709)
                    ·
                      rfl

theorem cell22_178834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 2, 1, 4, 3].length) (baseStart_178834 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_178834 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_178834 prefixEnd_178834 := by exact prefixLift 178834
  have htrace : WordTrace (prefixWord ++ tailWord_178834) baseStart_178834 baseEnd_178834 := by
    simpa [prefixWord, tailWord_178834, baseEnd_178834] using wordTrace_append hprefix tailTrace_178834
  have hstable : (prefixWord ++ tailWord_178834).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178834).length < 2 ^ (prefixWord ++ tailWord_178834).sum := by decide
  have hdescent : baseEnd_178834 < baseStart_178834 := by decide
  rcases family_descends (prefixWord ++ tailWord_178834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178954 : List Nat := [3, 1, 2, 2, 1, 2, 1, 6, 4]
def baseStart_178954 : Nat := 118140960795 + 178954 * 2 ^ 59
def prefixEnd_178954 : Nat := 4983230072969 + 3 ^ 40 * 178954 * 2
def baseEnd_178954 : Nat := 20419870454399572300447

theorem tailTrace_178954 : CollatzResearch.WordTrace tailWord_178954 prefixEnd_178954 20419870454399572300447 := by
  unfold tailWord_178954
  simp only [CollatzResearch.WordTrace]
  refine ⟨1631747148421923938767979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4351325729125130503381277 1631747148421923938767979)
  ·
    refine ⟨2447620722632885908151969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1631747148421923938767979 2447620722632885908151969)
    ·
      refine ⟨1835715541974664431113977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2447620722632885908151969 1835715541974664431113977)
      ·
        refine ⟨1376786656480998323335483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1835715541974664431113977 1376786656480998323335483)
        ·
          refine ⟨2065179984721497485003225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1376786656480998323335483 2065179984721497485003225)
          ·
            refine ⟨1548884988541123113752419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2065179984721497485003225 1548884988541123113752419)
            ·
              refine ⟨2323327482811684670628629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1548884988541123113752419 2323327482811684670628629)
              ·
                refine ⟨108905975756797718935717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2323327482811684670628629 108905975756797718935717)
                ·
                  refine ⟨20419870454399572300447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 108905975756797718935717 20419870454399572300447)
                  ·
                    rfl

theorem cell22_178954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 6, 4].length) (baseStart_178954 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_178954 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_178954 prefixEnd_178954 := by exact prefixLift 178954
  have htrace : WordTrace (prefixWord ++ tailWord_178954) baseStart_178954 baseEnd_178954 := by
    simpa [prefixWord, tailWord_178954, baseEnd_178954] using wordTrace_append hprefix tailTrace_178954
  have hstable : (prefixWord ++ tailWord_178954).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178954).length < 2 ^ (prefixWord ++ tailWord_178954).sum := by decide
  have hdescent : baseEnd_178954 < baseStart_178954 := by decide
  rcases family_descends (prefixWord ++ tailWord_178954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178973 : List Nat := [1, 4, 2, 4, 1, 1, 2, 2, 1, 4]
def baseStart_178973 : Nat := 118140960795 + 178973 * 2 ^ 59
def prefixEnd_178973 : Nat := 4983230072969 + 3 ^ 40 * 178973 * 2
def baseEnd_178973 : Nat := 61266115451489000676283

theorem tailTrace_178973 : CollatzResearch.WordTrace tailWord_178973 prefixEnd_178973 61266115451489000676283 := by
  unfold tailWord_178973
  simp only [CollatzResearch.WordTrace]
  refine ⟨6527681580618862000013573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4351787720412574666675715 6527681580618862000013573)
  ·
    refine ⟨1223940296366036625002545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6527681580618862000013573 1223940296366036625002545)
    ·
      refine ⟨917955222274527468751909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1223940296366036625002545 917955222274527468751909)
      ·
        refine ⟨172116604176473900390983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 917955222274527468751909 172116604176473900390983)
        ·
          refine ⟨258174906264710850586475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 172116604176473900390983 258174906264710850586475)
          ·
            refine ⟨387262359397066275879713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 258174906264710850586475 387262359397066275879713)
            ·
              refine ⟨290446769547799706909785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 387262359397066275879713 290446769547799706909785)
              ·
                refine ⟨217835077160849780182339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 290446769547799706909785 217835077160849780182339)
                ·
                  refine ⟨326752615741274670273509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 217835077160849780182339 326752615741274670273509)
                  ·
                    refine ⟨61266115451489000676283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 326752615741274670273509 61266115451489000676283)
                    ·
                      rfl

theorem cell22_178973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 2, 2, 1, 4].length) (baseStart_178973 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_178973 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_178973 prefixEnd_178973 := by exact prefixLift 178973
  have htrace : WordTrace (prefixWord ++ tailWord_178973) baseStart_178973 baseEnd_178973 := by
    simpa [prefixWord, tailWord_178973, baseEnd_178973] using wordTrace_append hprefix tailTrace_178973
  have hstable : (prefixWord ++ tailWord_178973).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178973).length < 2 ^ (prefixWord ++ tailWord_178973).sum := by decide
  have hdescent : baseEnd_178973 < baseStart_178973 := by decide
  rcases family_descends (prefixWord ++ tailWord_178973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178984 : List Nat := [2, 1, 5, 1, 1, 1, 2, 3, 2, 4]
def baseStart_178984 : Nat := 118140960795 + 178984 * 2 ^ 59
def prefixEnd_178984 : Nat := 4983230072969 + 3 ^ 40 * 178984 * 2
def baseEnd_178984 : Nat := 61269880976288638651249

theorem tailTrace_178984 : CollatzResearch.WordTrace tailWord_178984 prefixEnd_178984 61269880976288638651249 := by
  unfold tailWord_178984
  simp only [CollatzResearch.WordTrace]
  refine ⟨3264041391789505439332003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4352055189052673919109337 3264041391789505439332003)
  ·
    refine ⟨4896062087684258158998005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3264041391789505439332003 4896062087684258158998005)
    ·
      refine ⟨459005820720399202406063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4896062087684258158998005 459005820720399202406063)
      ·
        refine ⟨688508731080598803609095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 459005820720399202406063 688508731080598803609095)
        ·
          refine ⟨1032763096620898205413643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 688508731080598803609095 1032763096620898205413643)
          ·
            refine ⟨1549144644931347308120465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1032763096620898205413643 1549144644931347308120465)
            ·
              refine ⟨1161858483698510481090349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1549144644931347308120465 1161858483698510481090349)
              ·
                refine ⟨435696931386941430408881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1161858483698510481090349 435696931386941430408881)
                ·
                  refine ⟨326772698540206072806661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 435696931386941430408881 326772698540206072806661)
                  ·
                    refine ⟨61269880976288638651249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 326772698540206072806661 61269880976288638651249)
                    ·
                      rfl

theorem cell22_178984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 3, 2, 4].length) (baseStart_178984 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_178984 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_178984 prefixEnd_178984 := by exact prefixLift 178984
  have htrace : WordTrace (prefixWord ++ tailWord_178984) baseStart_178984 baseEnd_178984 := by
    simpa [prefixWord, tailWord_178984, baseEnd_178984] using wordTrace_append hprefix tailTrace_178984
  have hstable : (prefixWord ++ tailWord_178984).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178984).length < 2 ^ (prefixWord ++ tailWord_178984).sum := by decide
  have hdescent : baseEnd_178984 < baseStart_178984 := by decide
  rcases family_descends (prefixWord ++ tailWord_178984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179061 : List Nat := [1, 3, 4, 1, 1, 3, 2, 2, 5]
def baseStart_179061 : Nat := 118140960795 + 179061 * 2 ^ 59
def prefixEnd_179061 : Nat := 4983230072969 + 3 ^ 40 * 179061 * 2
def baseEnd_179061 : Nat := 20432079883295368158671

theorem tailTrace_179061 : CollatzResearch.WordTrace tailWord_179061 prefixEnd_179061 20432079883295368158671 := by
  unfold tailWord_179061
  simp only [CollatzResearch.WordTrace]
  refine ⟨6530891204300053029217037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4353927469533368686144691 6530891204300053029217037)
  ·
    refine ⟨2449084201612519885956389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6530891204300053029217037 2449084201612519885956389)
    ·
      refine ⟨459203287802347478616823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2449084201612519885956389 459203287802347478616823)
      ·
        refine ⟨688804931703521217925235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 459203287802347478616823 688804931703521217925235)
        ·
          refine ⟨1033207397555281826887853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 688804931703521217925235 1033207397555281826887853)
          ·
            refine ⟨387452774083230685082945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1033207397555281826887853 387452774083230685082945)
            ·
              refine ⟨290589580562423013812209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 387452774083230685082945 290589580562423013812209)
              ·
                refine ⟨217942185421817260359157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 290589580562423013812209 217942185421817260359157)
                ·
                  refine ⟨20432079883295368158671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 217942185421817260359157 20432079883295368158671)
                  ·
                    rfl

theorem cell22_179061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 2, 2, 5].length) (baseStart_179061 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_179061 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_179061 prefixEnd_179061 := by exact prefixLift 179061
  have htrace : WordTrace (prefixWord ++ tailWord_179061) baseStart_179061 baseEnd_179061 := by
    simpa [prefixWord, tailWord_179061, baseEnd_179061] using wordTrace_append hprefix tailTrace_179061
  have hstable : (prefixWord ++ tailWord_179061).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179061).length < 2 ^ (prefixWord ++ tailWord_179061).sum := by decide
  have hdescent : baseEnd_179061 < baseStart_179061 := by decide
  rcases family_descends (prefixWord ++ tailWord_179061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179065 : List Nat := [1, 2, 1, 3, 2, 5, 2, 2, 1, 3]
def baseStart_179065 : Nat := 118140960795 + 179065 * 2 ^ 59
def prefixEnd_179065 : Nat := 4983230072969 + 3 ^ 40 * 179065 * 2
def baseEnd_179065 : Nat := 61297608931631427376001

theorem tailTrace_179065 : CollatzResearch.WordTrace tailWord_179065 prefixEnd_179065 61297608931631427376001 := by
  unfold tailWord_179065
  simp only [CollatzResearch.WordTrace]
  refine ⟨6531037096285561712362649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4354024730857041141575099 6531037096285561712362649)
  ·
    refine ⟨4898277822214171284271987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6531037096285561712362649 4898277822214171284271987)
    ·
      refine ⟨7347416733321256926407981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4898277822214171284271987 7347416733321256926407981)
      ·
        refine ⟨2755281274995471347402993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7347416733321256926407981 2755281274995471347402993)
        ·
          refine ⟨2066460956246603510552245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2755281274995471347402993 2066460956246603510552245)
          ·
            refine ⟨193730714648119079114273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2066460956246603510552245 193730714648119079114273)
            ·
              refine ⟨145298035986089309335705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 193730714648119079114273 145298035986089309335705)
              ·
                refine ⟨108973526989566982001779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 145298035986089309335705 108973526989566982001779)
                ·
                  refine ⟨163460290484350473002669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 108973526989566982001779 163460290484350473002669)
                  ·
                    refine ⟨61297608931631427376001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 163460290484350473002669 61297608931631427376001)
                    ·
                      rfl

theorem cell22_179065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 2, 2, 1, 3].length) (baseStart_179065 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_179065 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_179065 prefixEnd_179065 := by exact prefixLift 179065
  have htrace : WordTrace (prefixWord ++ tailWord_179065) baseStart_179065 baseEnd_179065 := by
    simpa [prefixWord, tailWord_179065, baseEnd_179065] using wordTrace_append hprefix tailTrace_179065
  have hstable : (prefixWord ++ tailWord_179065).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179065).length < 2 ^ (prefixWord ++ tailWord_179065).sum := by decide
  have hdescent : baseEnd_179065 < baseStart_179065 := by decide
  rcases family_descends (prefixWord ++ tailWord_179065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
