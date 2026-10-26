import V185TrunkScan23Chunk0892

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5285532 : List Nat := [2, 2, 3, 2, 3, 1, 2, 1, 3, 4]
def baseStart_5285532 : Nat := 118140960795 + 5285532 * 2 ^ 59
def prefixEnd_5285532 : Nat := 4983230072969 + 3 ^ 40 * 5285532 * 2
def baseEnd_5285532 : Nat := 904672810240039855147429

theorem tailTrace_5285532 : CollatzResearch.WordTrace tailWord_5285532 prefixEnd_5285532 904672810240039855147429 := by
  unfold tailWord_5285532
  simp only [CollatzResearch.WordTrace]
  refine ⟨96389594743713867921665425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128519459658285157228887233 96389594743713867921665425)
  ·
    refine ⟨72292196057785400941249069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96389594743713867921665425 72292196057785400941249069)
    ·
      refine ⟨27109573521669525352968401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72292196057785400941249069 27109573521669525352968401)
      ·
        refine ⟨20332180141252144014726301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27109573521669525352968401 20332180141252144014726301)
        ·
          refine ⟨7624567552969554005522363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20332180141252144014726301 7624567552969554005522363)
          ·
            refine ⟨11436851329454331008283545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7624567552969554005522363 11436851329454331008283545)
            ·
              refine ⟨8577638497090748256212659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11436851329454331008283545 8577638497090748256212659)
              ·
                refine ⟨12866457745636122384318989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8577638497090748256212659 12866457745636122384318989)
                ·
                  refine ⟨4824921654613545894119621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12866457745636122384318989 4824921654613545894119621)
                  ·
                    refine ⟨904672810240039855147429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4824921654613545894119621 904672810240039855147429)
                    ·
                      rfl

theorem cell23_5285532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 2, 1, 3, 4].length) (baseStart_5285532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5285532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5285532 prefixEnd_5285532 := by exact prefixLift 5285532
  have htrace : WordTrace (prefixWord ++ tailWord_5285532) baseStart_5285532 baseEnd_5285532 := by
    simpa [prefixWord, tailWord_5285532, baseEnd_5285532] using wordTrace_append hprefix tailTrace_5285532
  have hstable : (prefixWord ++ tailWord_5285532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5285532).length < 2 ^ (prefixWord ++ tailWord_5285532).sum := by decide
  have hdescent : baseEnd_5285532 < baseStart_5285532 := by decide
  rcases family_descends (prefixWord ++ tailWord_5285532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5285555 : List Nat := [1, 1, 1, 2, 3, 3, 1, 4, 3, 1, 3]
def baseStart_5285555 : Nat := 118140960795 + 5285555 * 2 ^ 59
def prefixEnd_5285555 : Nat := 4983230072969 + 3 ^ 40 * 5285555 * 2
def baseEnd_5285555 : Nat := 2714030240775172975454681

theorem tailTrace_5285555 : CollatzResearch.WordTrace tailWord_5285555 prefixEnd_5285555 2714030240775172975454681 := by
  unfold tailWord_5285555
  simp only [CollatzResearch.WordTrace]
  refine ⟨192780028366344410771418119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128520018910896273847612079 192780028366344410771418119)
  ·
    refine ⟨289170042549516616157127179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192780028366344410771418119 289170042549516616157127179)
    ·
      refine ⟨433755063824274924235690769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 289170042549516616157127179 433755063824274924235690769)
      ·
        refine ⟨325316297868206193176768077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 433755063824274924235690769 325316297868206193176768077)
        ·
          refine ⟨121993611700577322441288029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 325316297868206193176768077 121993611700577322441288029)
          ·
            refine ⟨45747604387716495915483011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 121993611700577322441288029 45747604387716495915483011)
            ·
              refine ⟨68621406581574743873224517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45747604387716495915483011 68621406581574743873224517)
              ·
                refine ⟨12866513734045264476229597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 68621406581574743873224517 12866513734045264476229597)
                ·
                  refine ⟨4824942650266974178586099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12866513734045264476229597 4824942650266974178586099)
                  ·
                    refine ⟨7237413975400461267879149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4824942650266974178586099 7237413975400461267879149)
                    ·
                      refine ⟨2714030240775172975454681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7237413975400461267879149 2714030240775172975454681)
                      ·
                        rfl

theorem cell23_5285555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 4, 3, 1, 3].length) (baseStart_5285555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5285555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5285555 prefixEnd_5285555 := by exact prefixLift 5285555
  have htrace : WordTrace (prefixWord ++ tailWord_5285555) baseStart_5285555 baseEnd_5285555 := by
    simpa [prefixWord, tailWord_5285555, baseEnd_5285555] using wordTrace_append hprefix tailTrace_5285555
  have hstable : (prefixWord ++ tailWord_5285555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5285555).length < 2 ^ (prefixWord ++ tailWord_5285555).sum := by decide
  have hdescent : baseEnd_5285555 < baseStart_5285555 := by decide
  rcases family_descends (prefixWord ++ tailWord_5285555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5285565 : List Nat := [1, 4, 1, 2, 1, 2, 1, 3, 1, 5, 2]
def baseStart_5285565 : Nat := 118140960795 + 5285565 * 2 ^ 59
def prefixEnd_5285565 : Nat := 4983230072969 + 3 ^ 40 * 5285565 * 2
def baseEnd_5285565 : Nat := 2714035375581717936329635

theorem tailTrace_5285565 : CollatzResearch.WordTrace tailWord_5285565 prefixEnd_5285565 2714035375581717936329635 := by
  unfold tailWord_5285565
  simp only [CollatzResearch.WordTrace]
  refine ⟨192780393096308182479282149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128520262064205454986188099 192780393096308182479282149)
  ·
    refine ⟨36146323705557784214865403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 192780393096308182479282149 36146323705557784214865403)
    ·
      refine ⟨54219485558336676322298105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36146323705557784214865403 54219485558336676322298105)
      ·
        refine ⟨40664614168752507241723579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54219485558336676322298105 40664614168752507241723579)
        ·
          refine ⟨60996921253128760862585369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40664614168752507241723579 60996921253128760862585369)
          ·
            refine ⟨45747690939846570646939027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60996921253128760862585369 45747690939846570646939027)
            ·
              refine ⟨68621536409769855970408541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45747690939846570646939027 68621536409769855970408541)
              ·
                refine ⟨25733076153663695988903203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 68621536409769855970408541 25733076153663695988903203)
                ·
                  refine ⟨38599614230495543983354805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25733076153663695988903203 38599614230495543983354805)
                  ·
                    refine ⟨3618713834108957248439513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 38599614230495543983354805 3618713834108957248439513)
                    ·
                      refine ⟨2714035375581717936329635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3618713834108957248439513 2714035375581717936329635)
                      ·
                        rfl

theorem cell23_5285565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 3, 1, 5, 2].length) (baseStart_5285565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5285565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5285565 prefixEnd_5285565 := by exact prefixLift 5285565
  have htrace : WordTrace (prefixWord ++ tailWord_5285565) baseStart_5285565 baseEnd_5285565 := by
    simpa [prefixWord, tailWord_5285565, baseEnd_5285565] using wordTrace_append hprefix tailTrace_5285565
  have hstable : (prefixWord ++ tailWord_5285565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5285565).length < 2 ^ (prefixWord ++ tailWord_5285565).sum := by decide
  have hdescent : baseEnd_5285565 < baseStart_5285565 := by decide
  rcases family_descends (prefixWord ++ tailWord_5285565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5285582 : List Nat := [4, 1, 1, 1, 3, 1, 3, 2, 2, 3, 2]
def baseStart_5285582 : Nat := 118140960795 + 5285582 * 2 ^ 59
def prefixEnd_5285582 : Nat := 4983230072969 + 3 ^ 40 * 5285582 * 2
def baseEnd_5285582 : Nat := 2714044104752844369817057

theorem tailTrace_5285582 : CollatzResearch.WordTrace tailWord_5285582 prefixEnd_5285582 2714044104752844369817057 := by
  unfold tailWord_5285582
  simp only [CollatzResearch.WordTrace]
  refine ⟨24097626642155824297831375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 128520675424831062921767333 24097626642155824297831375)
  ·
    refine ⟨36146439963233736446747063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24097626642155824297831375 36146439963233736446747063)
    ·
      refine ⟨54219659944850604670120595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36146439963233736446747063 54219659944850604670120595)
      ·
        refine ⟨81329489917275907005180893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54219659944850604670120595 81329489917275907005180893)
        ·
          refine ⟨30498558718978465126942835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81329489917275907005180893 30498558718978465126942835)
          ·
            refine ⟨45747838078467697690414253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30498558718978465126942835 45747838078467697690414253)
            ·
              refine ⟨17155439279425386633905345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45747838078467697690414253 17155439279425386633905345)
              ·
                refine ⟨12866579459569039975429009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17155439279425386633905345 12866579459569039975429009)
                ·
                  refine ⟨9649934594676779981571757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12866579459569039975429009 9649934594676779981571757)
                  ·
                    refine ⟨3618725473003792493089409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9649934594676779981571757 3618725473003792493089409)
                    ·
                      refine ⟨2714044104752844369817057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3618725473003792493089409 2714044104752844369817057)
                      ·
                        rfl

theorem cell23_5285582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 3, 2, 2, 3, 2].length) (baseStart_5285582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5285582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5285582 prefixEnd_5285582 := by exact prefixLift 5285582
  have htrace : WordTrace (prefixWord ++ tailWord_5285582) baseStart_5285582 baseEnd_5285582 := by
    simpa [prefixWord, tailWord_5285582, baseEnd_5285582] using wordTrace_append hprefix tailTrace_5285582
  have hstable : (prefixWord ++ tailWord_5285582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5285582).length < 2 ^ (prefixWord ++ tailWord_5285582).sum := by decide
  have hdescent : baseEnd_5285582 < baseStart_5285582 := by decide
  rcases family_descends (prefixWord ++ tailWord_5285582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5285596 : List Nat := [2, 2, 5, 1, 3, 1, 2, 1, 6]
def baseStart_5285596 : Nat := 118140960795 + 5285596 * 2 ^ 59
def prefixEnd_5285596 : Nat := 4983230072969 + 3 ^ 40 * 5285596 * 2
def baseEnd_5285596 : Nat := 301561254831334146115777

theorem tailTrace_5285596 : CollatzResearch.WordTrace tailWord_5285596 prefixEnd_5285596 301561254831334146115777 := by
  unfold tailWord_5285596
  simp only [CollatzResearch.WordTrace]
  refine ⟨96390761879597937386830321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128521015839463916515773761 96390761879597937386830321)
  ·
    refine ⟨72293071409698453040122741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96390761879597937386830321 72293071409698453040122741)
    ·
      refine ⟨6777475444659229972511507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 72293071409698453040122741 6777475444659229972511507)
      ·
        refine ⟨10166213166988844958767261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6777475444659229972511507 10166213166988844958767261)
        ·
          refine ⟨3812329937620816859537723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10166213166988844958767261 3812329937620816859537723)
          ·
            refine ⟨5718494906431225289306585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3812329937620816859537723 5718494906431225289306585)
            ·
              refine ⟨4288871179823418966979939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5718494906431225289306585 4288871179823418966979939)
              ·
                refine ⟨6433306769735128450469909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4288871179823418966979939 6433306769735128450469909)
                ·
                  refine ⟨301561254831334146115777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6433306769735128450469909 301561254831334146115777)
                  ·
                    rfl

theorem cell23_5285596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 2, 1, 6].length) (baseStart_5285596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5285596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5285596 prefixEnd_5285596 := by exact prefixLift 5285596
  have htrace : WordTrace (prefixWord ++ tailWord_5285596) baseStart_5285596 baseEnd_5285596 := by
    simpa [prefixWord, tailWord_5285596, baseEnd_5285596] using wordTrace_append hprefix tailTrace_5285596
  have hstable : (prefixWord ++ tailWord_5285596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5285596).length < 2 ^ (prefixWord ++ tailWord_5285596).sum := by decide
  have hdescent : baseEnd_5285596 < baseStart_5285596 := by decide
  rcases family_descends (prefixWord ++ tailWord_5285596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5285612 : List Nat := [2, 2, 1, 1, 2, 2, 2, 4, 3, 2, 2]
def baseStart_5285612 : Nat := 118140960795 + 5285612 * 2 ^ 59
def prefixEnd_5285612 : Nat := 4983230072969 + 3 ^ 40 * 5285612 * 2
def baseEnd_5285612 : Nat := 2714059509172479252441919

theorem tailTrace_5285612 : CollatzResearch.WordTrace tailWord_5285612 prefixEnd_5285612 2714059509172479252441919 := by
  unfold tailWord_5285612
  simp only [CollatzResearch.WordTrace]
  refine ⟨96391053663568954753121545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128521404884758606337495393 96391053663568954753121545)
  ·
    refine ⟨72293290247676716064841159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96391053663568954753121545 72293290247676716064841159)
    ·
      refine ⟨108439935371515074097261739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72293290247676716064841159 108439935371515074097261739)
      ·
        refine ⟨162659903057272611145892609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108439935371515074097261739 162659903057272611145892609)
        ·
          refine ⟨121994927292954458359419457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 162659903057272611145892609 121994927292954458359419457)
          ·
            refine ⟨91496195469715843769564593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 121994927292954458359419457 91496195469715843769564593)
            ·
              refine ⟨68622146602286882827173445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91496195469715843769564593 68622146602286882827173445)
              ·
                refine ⟨12866652487928790530095021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 68622146602286882827173445 12866652487928790530095021)
                ·
                  refine ⟨4824994682973296448785633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12866652487928790530095021 4824994682973296448785633)
                  ·
                    refine ⟨3618746012229972336589225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4824994682973296448785633 3618746012229972336589225)
                    ·
                      refine ⟨2714059509172479252441919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3618746012229972336589225 2714059509172479252441919)
                      ·
                        rfl

theorem cell23_5285612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 2, 2].length) (baseStart_5285612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5285612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5285612 prefixEnd_5285612 := by exact prefixLift 5285612
  have htrace : WordTrace (prefixWord ++ tailWord_5285612) baseStart_5285612 baseEnd_5285612 := by
    simpa [prefixWord, tailWord_5285612, baseEnd_5285612] using wordTrace_append hprefix tailTrace_5285612
  have hstable : (prefixWord ++ tailWord_5285612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5285612).length < 2 ^ (prefixWord ++ tailWord_5285612).sum := by decide
  have hdescent : baseEnd_5285612 < baseStart_5285612 := by decide
  rcases family_descends (prefixWord ++ tailWord_5285612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5285615 : List Nat := [1, 1, 2, 1, 5, 1, 3, 1, 3, 2, 3]
def baseStart_5285615 : Nat := 118140960795 + 5285615 * 2 ^ 59
def prefixEnd_5285615 : Nat := 4983230072969 + 3 ^ 40 * 5285615 * 2
def baseEnd_5285615 : Nat := 2714061049614442740704405

theorem tailTrace_5285615 : CollatzResearch.WordTrace tailWord_5285615 prefixEnd_5285615 2714061049614442740704405 := by
  unfold tailWord_5285615
  simp only [CollatzResearch.WordTrace]
  refine ⟨192782216746127041018602299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128521477830751360679068199 192782216746127041018602299)
  ·
    refine ⟨289173325119190561527903449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192782216746127041018602299 289173325119190561527903449)
    ·
      refine ⟨216879993839392921145927587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 289173325119190561527903449 216879993839392921145927587)
      ·
        refine ⟨325319990759089381718891381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 216879993839392921145927587 325319990759089381718891381)
        ·
          refine ⟨30498749133664629536146067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 325319990759089381718891381 30498749133664629536146067)
          ·
            refine ⟨45748123700496944304219101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30498749133664629536146067 45748123700496944304219101)
            ·
              refine ⟨17155546387686354114082163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45748123700496944304219101 17155546387686354114082163)
              ·
                refine ⟨25733319581529531171123245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17155546387686354114082163 25733319581529531171123245)
                ·
                  refine ⟨9649994843073574189171217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25733319581529531171123245 9649994843073574189171217)
                  ·
                    refine ⟨7237496132305180641878413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9649994843073574189171217 7237496132305180641878413)
                    ·
                      refine ⟨2714061049614442740704405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7237496132305180641878413 2714061049614442740704405)
                      ·
                        rfl

theorem cell23_5285615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 3, 1, 3, 2, 3].length) (baseStart_5285615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5285615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5285615 prefixEnd_5285615 := by exact prefixLift 5285615
  have htrace : WordTrace (prefixWord ++ tailWord_5285615) baseStart_5285615 baseEnd_5285615 := by
    simpa [prefixWord, tailWord_5285615, baseEnd_5285615] using wordTrace_append hprefix tailTrace_5285615
  have hstable : (prefixWord ++ tailWord_5285615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5285615).length < 2 ^ (prefixWord ++ tailWord_5285615).sum := by decide
  have hdescent : baseEnd_5285615 < baseStart_5285615 := by decide
  rcases family_descends (prefixWord ++ tailWord_5285615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5285618 : List Nat := [3, 2, 1, 3, 1, 1, 1, 11]
def baseStart_5285618 : Nat := 118140960795 + 5285618 * 2 ^ 59
def prefixEnd_5285618 : Nat := 4983230072969 + 3 ^ 40 * 5285618 * 2
def baseEnd_5285618 : Nat := 100520836668755786258033

theorem tailTrace_5285618 : CollatzResearch.WordTrace tailWord_5285618 prefixEnd_5285618 100520836668755786258033 := by
  unfold tailWord_5285618
  simp only [CollatzResearch.WordTrace]
  refine ⟨48195581541279043132740377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128521550776744115020641005 48195581541279043132740377)
  ·
    refine ⟨36146686155959282349555283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48195581541279043132740377 36146686155959282349555283)
    ·
      refine ⟨54220029233938923524332925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36146686155959282349555283 54220029233938923524332925)
      ·
        refine ⟨20332510962727096321624847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54220029233938923524332925 20332510962727096321624847)
        ·
          refine ⟨30498766444090644482437271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20332510962727096321624847 30498766444090644482437271)
          ·
            refine ⟨45748149666135966723655907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30498766444090644482437271 45748149666135966723655907)
            ·
              refine ⟨68622224499203950085483861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45748149666135966723655907 68622224499203950085483861)
              ·
                refine ⟨100520836668755786258033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 68622224499203950085483861 100520836668755786258033)
                ·
                  rfl

theorem cell23_5285618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 11].length) (baseStart_5285618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5285618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5285618 prefixEnd_5285618 := by exact prefixLift 5285618
  have htrace : WordTrace (prefixWord ++ tailWord_5285618) baseStart_5285618 baseEnd_5285618 := by
    simpa [prefixWord, tailWord_5285618, baseEnd_5285618] using wordTrace_append hprefix tailTrace_5285618
  have hstable : (prefixWord ++ tailWord_5285618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5285618).length < 2 ^ (prefixWord ++ tailWord_5285618).sum := by decide
  have hdescent : baseEnd_5285618 < baseStart_5285618 := by decide
  rcases family_descends (prefixWord ++ tailWord_5285618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5285639 : List Nat := [1, 1, 4, 4, 2, 1, 2, 2, 2, 4]
def baseStart_5285639 : Nat := 118140960795 + 5285639 * 2 ^ 59
def prefixEnd_5285639 : Nat := 4983230072969 + 3 ^ 40 * 5285639 * 2
def baseEnd_5285639 : Nat := 904691124383383548934765

theorem tailTrace_5285639 : CollatzResearch.WordTrace tailWord_5285639 prefixEnd_5285639 904691124383383548934765 := by
  unfold tailWord_5285639
  simp only [CollatzResearch.WordTrace]
  refine ⟨192783092098040093117475971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128522061398693395411650647 192783092098040093117475971)
  ·
    refine ⟨289174638147060139676213957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192783092098040093117475971 289174638147060139676213957)
    ·
      refine ⟨54220244652573776189290117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 289174638147060139676213957 54220244652573776189290117)
      ·
        refine ⟨10166295872357583035491897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54220244652573776189290117 10166295872357583035491897)
        ·
          refine ⟨7624721904268187276618923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10166295872357583035491897 7624721904268187276618923)
          ·
            refine ⟨11437082856402280914928385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7624721904268187276618923 11437082856402280914928385)
            ·
              refine ⟨8577812142301710686196289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11437082856402280914928385 8577812142301710686196289)
              ·
                refine ⟨6433359106726283014647217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8577812142301710686196289 6433359106726283014647217)
                ·
                  refine ⟨4825019330044712260985413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6433359106726283014647217 4825019330044712260985413)
                  ·
                    refine ⟨904691124383383548934765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4825019330044712260985413 904691124383383548934765)
                    ·
                      rfl

theorem cell23_5285639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 2, 2, 2, 4].length) (baseStart_5285639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5285639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5285639 prefixEnd_5285639 := by exact prefixLift 5285639
  have htrace : WordTrace (prefixWord ++ tailWord_5285639) baseStart_5285639 baseEnd_5285639 := by
    simpa [prefixWord, tailWord_5285639, baseEnd_5285639] using wordTrace_append hprefix tailTrace_5285639
  have hstable : (prefixWord ++ tailWord_5285639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5285639).length < 2 ^ (prefixWord ++ tailWord_5285639).sum := by decide
  have hdescent : baseEnd_5285639 < baseStart_5285639 := by decide
  rcases family_descends (prefixWord ++ tailWord_5285639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5285765 : List Nat := [1, 3, 1, 1, 3, 2, 3, 1, 1, 2, 5]
def baseStart_5285765 : Nat := 118140960795 + 5285765 * 2 ^ 59
def prefixEnd_5285765 : Nat := 4983230072969 + 3 ^ 40 * 5285765 * 2
def baseEnd_5285765 : Nat := 2714138071712617153828715

theorem tailTrace_5285765 : CollatzResearch.WordTrace tailWord_5285765 prefixEnd_5285765 2714138071712617153828715 := by
  unfold tailWord_5285765
  simp only [CollatzResearch.WordTrace]
  refine ⟨192787687695583616636562749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128525125130389077757708499 192787687695583616636562749)
  ·
    refine ⟨72295382885843856238711031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 192787687695583616636562749 72295382885843856238711031)
    ·
      refine ⟨108443074328765784358066547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72295382885843856238711031 108443074328765784358066547)
      ·
        refine ⟨162664611493148676537099821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108443074328765784358066547 162664611493148676537099821)
        ·
          refine ⟨60999229309930753701412433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 162664611493148676537099821 60999229309930753701412433)
          ·
            refine ⟨45749421982448065276059325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60999229309930753701412433 45749421982448065276059325)
            ·
              refine ⟨17156033243418024478522247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45749421982448065276059325 17156033243418024478522247)
              ·
                refine ⟨25734049865127036717783371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17156033243418024478522247 25734049865127036717783371)
                ·
                  refine ⟨38601074797690555076675057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25734049865127036717783371 38601074797690555076675057)
                  ·
                    refine ⟨28950806098267916307506293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 38601074797690555076675057 28950806098267916307506293)
                    ·
                      refine ⟨2714138071712617153828715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28950806098267916307506293 2714138071712617153828715)
                      ·
                        rfl

theorem cell23_5285765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 3, 1, 1, 2, 5].length) (baseStart_5285765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5285765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5285765 prefixEnd_5285765 := by exact prefixLift 5285765
  have htrace : WordTrace (prefixWord ++ tailWord_5285765) baseStart_5285765 baseEnd_5285765 := by
    simpa [prefixWord, tailWord_5285765, baseEnd_5285765] using wordTrace_append hprefix tailTrace_5285765
  have hstable : (prefixWord ++ tailWord_5285765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5285765).length < 2 ^ (prefixWord ++ tailWord_5285765).sum := by decide
  have hdescent : baseEnd_5285765 < baseStart_5285765 := by decide
  rcases family_descends (prefixWord ++ tailWord_5285765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5285770 : List Nat := [3, 1, 2, 4, 2, 2, 2, 1, 2, 2, 2]
def baseStart_5285770 : Nat := 118140960795 + 5285770 * 2 ^ 59
def prefixEnd_5285770 : Nat := 4983230072969 + 3 ^ 40 * 5285770 * 2
def baseEnd_5285770 : Nat := 2714140639115889634266193

theorem tailTrace_5285770 : CollatzResearch.WordTrace tailWord_5285770 prefixEnd_5285770 2714140639115889634266193 := by
  unfold tailWord_5285770
  simp only [CollatzResearch.WordTrace]
  refine ⟨48196967515141375622623691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128525246707043668326996509 48196967515141375622623691)
  ·
    refine ⟨72295451272712063433935537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48196967515141375622623691 72295451272712063433935537)
    ·
      refine ⟨54221588454534047575451653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72295451272712063433935537 54221588454534047575451653)
      ·
        refine ⟨10166547835225133920397185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54221588454534047575451653 10166547835225133920397185)
        ·
          refine ⟨7624910876418850440297889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10166547835225133920397185 7624910876418850440297889)
          ·
            refine ⟨5718683157314137830223417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7624910876418850440297889 5718683157314137830223417)
            ·
              refine ⟨4289012367985603372667563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5718683157314137830223417 4289012367985603372667563)
              ·
                refine ⟨6433518551978405059001345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4289012367985603372667563 6433518551978405059001345)
                ·
                  refine ⟨4825138913983803794251009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6433518551978405059001345 4825138913983803794251009)
                  ·
                    refine ⟨3618854185487852845688257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4825138913983803794251009 3618854185487852845688257)
                    ·
                      refine ⟨2714140639115889634266193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3618854185487852845688257 2714140639115889634266193)
                      ·
                        rfl

theorem cell23_5285770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 2, 1, 2, 2, 2].length) (baseStart_5285770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5285770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5285770 prefixEnd_5285770 := by exact prefixLift 5285770
  have htrace : WordTrace (prefixWord ++ tailWord_5285770) baseStart_5285770 baseEnd_5285770 := by
    simpa [prefixWord, tailWord_5285770, baseEnd_5285770] using wordTrace_append hprefix tailTrace_5285770
  have hstable : (prefixWord ++ tailWord_5285770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5285770).length < 2 ^ (prefixWord ++ tailWord_5285770).sum := by decide
  have hdescent : baseEnd_5285770 < baseStart_5285770 := by decide
  rcases family_descends (prefixWord ++ tailWord_5285770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5285792 : List Nat := [2, 1, 1, 4, 1, 1, 1, 2, 4, 4, 2]
def baseStart_5285792 : Nat := 118140960795 + 5285792 * 2 ^ 59
def prefixEnd_5285792 : Nat := 4983230072969 + 3 ^ 40 * 5285792 * 2
def baseEnd_5285792 : Nat := 2714151935690288548191091

theorem tailTrace_5285792 : CollatzResearch.WordTrace tailWord_5285792 prefixEnd_5285792 2714151935690288548191091 := by
  unfold tailWord_5285792
  simp only [CollatzResearch.WordTrace]
  refine ⟨96394336233242900123897815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128525781644323866831863753 96394336233242900123897815)
  ·
    refine ⟨144591504349864350185846723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96394336233242900123897815 144591504349864350185846723)
    ·
      refine ⟨216887256524796525278770085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144591504349864350185846723 216887256524796525278770085)
      ·
        refine ⟨40666360598399348489769391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 216887256524796525278770085 40666360598399348489769391)
        ·
          refine ⟨60999540897599022734654087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40666360598399348489769391 60999540897599022734654087)
          ·
            refine ⟨91499311346398534101981131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60999540897599022734654087 91499311346398534101981131)
            ·
              refine ⟨137248967019597801152971697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91499311346398534101981131 137248967019597801152971697)
              ·
                refine ⟨102936725264698350864728773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 137248967019597801152971697 102936725264698350864728773)
                ·
                  refine ⟨19300635987130940787136645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 102936725264698350864728773 19300635987130940787136645)
                  ·
                    refine ⟨3618869247587051397588121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19300635987130940787136645 3618869247587051397588121)
                    ·
                      refine ⟨2714151935690288548191091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3618869247587051397588121 2714151935690288548191091)
                      ·
                        rfl

theorem cell23_5285792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 2, 4, 4, 2].length) (baseStart_5285792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5285792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5285792 prefixEnd_5285792 := by exact prefixLift 5285792
  have htrace : WordTrace (prefixWord ++ tailWord_5285792) baseStart_5285792 baseEnd_5285792 := by
    simpa [prefixWord, tailWord_5285792, baseEnd_5285792] using wordTrace_append hprefix tailTrace_5285792
  have hstable : (prefixWord ++ tailWord_5285792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5285792).length < 2 ^ (prefixWord ++ tailWord_5285792).sum := by decide
  have hdescent : baseEnd_5285792 < baseStart_5285792 := by decide
  rcases family_descends (prefixWord ++ tailWord_5285792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5285832 : List Nat := [2, 1, 3, 1, 4, 1, 2, 3, 6]
def baseStart_5285832 : Nat := 118140960795 + 5285832 * 2 ^ 59
def prefixEnd_5285832 : Nat := 4983230072969 + 3 ^ 40 * 5285832 * 2
def baseEnd_5285832 : Nat := 301574719435163154632323

theorem tailTrace_5285832 : CollatzResearch.WordTrace tailWord_5285832 prefixEnd_5285832 301574719435163154632323 := by
  unfold tailWord_5285832
  simp only [CollatzResearch.WordTrace]
  refine ⟨96395065693170443539625875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128526754257560591386167833 96395065693170443539625875)
  ·
    refine ⟨144592598539755665309438813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96395065693170443539625875 144592598539755665309438813)
    ·
      refine ⟨54222224452408374491039555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 144592598539755665309438813 54222224452408374491039555)
      ·
        refine ⟨81333336678612561736559333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54222224452408374491039555 81333336678612561736559333)
        ·
          refine ⟨15250000627239855325604875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 81333336678612561736559333 15250000627239855325604875)
          ·
            refine ⟨22875000940859782988407313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15250000627239855325604875 22875000940859782988407313)
            ·
              refine ⟨17156250705644837241305485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22875000940859782988407313 17156250705644837241305485)
              ·
                refine ⟨6433594014616813965489557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17156250705644837241305485 6433594014616813965489557)
                ·
                  refine ⟨301574719435163154632323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6433594014616813965489557 301574719435163154632323)
                  ·
                    rfl

theorem cell23_5285832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 2, 3, 6].length) (baseStart_5285832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5285832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5285832 prefixEnd_5285832 := by exact prefixLift 5285832
  have htrace : WordTrace (prefixWord ++ tailWord_5285832) baseStart_5285832 baseEnd_5285832 := by
    simpa [prefixWord, tailWord_5285832, baseEnd_5285832] using wordTrace_append hprefix tailTrace_5285832
  have hstable : (prefixWord ++ tailWord_5285832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5285832).length < 2 ^ (prefixWord ++ tailWord_5285832).sum := by decide
  have hdescent : baseEnd_5285832 < baseStart_5285832 := by decide
  rcases family_descends (prefixWord ++ tailWord_5285832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5285846 : List Nat := [5, 2, 1, 1, 3, 1, 1, 1, 1, 4, 3]
def baseStart_5285846 : Nat := 118140960795 + 5285846 * 2 ^ 59
def prefixEnd_5285846 : Nat := 4983230072969 + 3 ^ 40 * 5285846 * 2
def baseEnd_5285846 : Nat := 2714179663645631336915843

theorem tailTrace_5285846 : CollatzResearch.WordTrace tailWord_5285846 prefixEnd_5285846 2714179663645631336915843 := by
  unfold tailWord_5285846
  simp only [CollatzResearch.WordTrace]
  refine ⟨12049415125518135466891337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 128527094672193444980174261 12049415125518135466891337)
  ·
    refine ⟨9037061344138601600168503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12049415125518135466891337 9037061344138601600168503)
    ·
      refine ⟨13555592016207902400252755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9037061344138601600168503 13555592016207902400252755)
      ·
        refine ⟨20333388024311853600379133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13555592016207902400252755 20333388024311853600379133)
        ·
          refine ⟨7625020509116945100142175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20333388024311853600379133 7625020509116945100142175)
          ·
            refine ⟨11437530763675417650213263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7625020509116945100142175 11437530763675417650213263)
            ·
              refine ⟨17156296145513126475319895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11437530763675417650213263 17156296145513126475319895)
              ·
                refine ⟨25734444218269689712979843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17156296145513126475319895 25734444218269689712979843)
                ·
                  refine ⟨38601666327404534569469765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25734444218269689712979843 38601666327404534569469765)
                  ·
                    refine ⟨7237812436388350231775581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 38601666327404534569469765 7237812436388350231775581)
                    ·
                      refine ⟨2714179663645631336915843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7237812436388350231775581 2714179663645631336915843)
                      ·
                        rfl

theorem cell23_5285846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 1, 1, 1, 4, 3].length) (baseStart_5285846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5285846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5285846 prefixEnd_5285846 := by exact prefixLift 5285846
  have htrace : WordTrace (prefixWord ++ tailWord_5285846) baseStart_5285846 baseEnd_5285846 := by
    simpa [prefixWord, tailWord_5285846, baseEnd_5285846] using wordTrace_append hprefix tailTrace_5285846
  have hstable : (prefixWord ++ tailWord_5285846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5285846).length < 2 ^ (prefixWord ++ tailWord_5285846).sum := by decide
  have hdescent : baseEnd_5285846 < baseStart_5285846 := by decide
  rcases family_descends (prefixWord ++ tailWord_5285846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5285853 : List Nat := [1, 4, 3, 1, 3, 1, 2, 3, 1, 4]
def baseStart_5285853 : Nat := 118140960795 + 5285853 * 2 ^ 59
def prefixEnd_5285853 : Nat := 4983230072969 + 3 ^ 40 * 5285853 * 2
def baseEnd_5285853 : Nat := 904727752670070936509437

theorem tailTrace_5285853 : CollatzResearch.WordTrace tailWord_5285853 prefixEnd_5285853 904727752670070936509437 := by
  unfold tailWord_5285853
  simp only [CollatzResearch.WordTrace]
  refine ⟨192790897319264807665766213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128527264879509871777177475 192790897319264807665766213)
  ·
    refine ⟨36148293247362151437331165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 192790897319264807665766213 36148293247362151437331165)
    ·
      refine ⟨13555609967760806788999187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36148293247362151437331165 13555609967760806788999187)
      ·
        refine ⟨20333414951641210183498781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13555609967760806788999187 20333414951641210183498781)
        ·
          refine ⟨7625030606865453818812043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20333414951641210183498781 7625030606865453818812043)
          ·
            refine ⟨11437545910298180728218065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7625030606865453818812043 11437545910298180728218065)
            ·
              refine ⟨8578159432723635546163549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11437545910298180728218065 8578159432723635546163549)
              ·
                refine ⟨3216809787271363329811331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8578159432723635546163549 3216809787271363329811331)
                ·
                  refine ⟨4825214680907044994716997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3216809787271363329811331 4825214680907044994716997)
                  ·
                    refine ⟨904727752670070936509437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4825214680907044994716997 904727752670070936509437)
                    ·
                      rfl

theorem cell23_5285853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 2, 3, 1, 4].length) (baseStart_5285853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5285853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5285853 prefixEnd_5285853 := by exact prefixLift 5285853
  have htrace : WordTrace (prefixWord ++ tailWord_5285853) baseStart_5285853 baseEnd_5285853 := by
    simpa [prefixWord, tailWord_5285853, baseEnd_5285853] using wordTrace_append hprefix tailTrace_5285853
  have hstable : (prefixWord ++ tailWord_5285853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5285853).length < 2 ^ (prefixWord ++ tailWord_5285853).sum := by decide
  have hdescent : baseEnd_5285853 < baseStart_5285853 := by decide
  rcases family_descends (prefixWord ++ tailWord_5285853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5285875 : List Nat := [1, 1, 1, 2, 2, 2, 1, 4, 3, 6]
def baseStart_5285875 : Nat := 118140960795 + 5285875 * 2 ^ 59
def prefixEnd_5285875 : Nat := 4983230072969 + 3 ^ 40 * 5285875 * 2
def baseEnd_5285875 : Nat := 904731518194870574484403

theorem tailTrace_5285875 : CollatzResearch.WordTrace tailWord_5285875 prefixEnd_5285875 904731518194870574484403 := by
  unfold tailWord_5285875
  simp only [CollatzResearch.WordTrace]
  refine ⟨192791699725185105423067079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128527799816790070282044719 192791699725185105423067079)
  ·
    refine ⟨289187549587777658134600619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192791699725185105423067079 289187549587777658134600619)
    ·
      refine ⟨433781324381666487201900929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 289187549587777658134600619 433781324381666487201900929)
      ·
        refine ⟨325335993286249865401425697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 433781324381666487201900929 325335993286249865401425697)
        ·
          refine ⟨244001994964687399051069273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 325335993286249865401425697 244001994964687399051069273)
          ·
            refine ⟨183001496223515549288301955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 244001994964687399051069273 183001496223515549288301955)
            ·
              refine ⟨274502244335273323932452933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 183001496223515549288301955 274502244335273323932452933)
              ·
                refine ⟨51469170812863748237334925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 274502244335273323932452933 51469170812863748237334925)
                ·
                  refine ⟨19300939054823905589000597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51469170812863748237334925 19300939054823905589000597)
                  ·
                    refine ⟨904731518194870574484403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19300939054823905589000597 904731518194870574484403)
                    ·
                      rfl

theorem cell23_5285875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 4, 3, 6].length) (baseStart_5285875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5285875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5285875 prefixEnd_5285875 := by exact prefixLift 5285875
  have htrace : WordTrace (prefixWord ++ tailWord_5285875) baseStart_5285875 baseEnd_5285875 := by
    simpa [prefixWord, tailWord_5285875, baseEnd_5285875] using wordTrace_append hprefix tailTrace_5285875
  have hstable : (prefixWord ++ tailWord_5285875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5285875).length < 2 ^ (prefixWord ++ tailWord_5285875).sum := by decide
  have hdescent : baseEnd_5285875 < baseStart_5285875 := by decide
  rcases family_descends (prefixWord ++ tailWord_5285875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5285886 : List Nat := [4, 2, 2, 2, 1, 1, 1, 2, 1, 5, 2]
def baseStart_5285886 : Nat := 118140960795 + 5285886 * 2 ^ 59
def prefixEnd_5285886 : Nat := 4983230072969 + 3 ^ 40 * 5285886 * 2
def baseEnd_5285886 : Nat := 2714200202871811180415659

theorem tailTrace_5285886 : CollatzResearch.WordTrace tailWord_5285886 prefixEnd_5285886 2714200202871811180415659 := by
  unfold tailWord_5285886
  simp only [CollatzResearch.WordTrace]
  refine ⟨24099012616018156787714689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 128528067285430169534478341 24099012616018156787714689)
  ·
    refine ⟨18074259462013617590786017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24099012616018156787714689 18074259462013617590786017)
    ·
      refine ⟨13555694596510213193089513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18074259462013617590786017 13555694596510213193089513)
      ·
        refine ⟨10166770947382659894817135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13555694596510213193089513 10166770947382659894817135)
        ·
          refine ⟨15250156421073989842225703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10166770947382659894817135 15250156421073989842225703)
          ·
            refine ⟨22875234631610984763338555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15250156421073989842225703 22875234631610984763338555)
            ·
              refine ⟨34312851947416477145007833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22875234631610984763338555 34312851947416477145007833)
              ·
                refine ⟨25734638960562357858755875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34312851947416477145007833 25734638960562357858755875)
                ·
                  refine ⟨38601958440843536788133813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25734638960562357858755875 38601958440843536788133813)
                  ·
                    refine ⟨3618933603829081573887545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 38601958440843536788133813 3618933603829081573887545)
                    ·
                      refine ⟨2714200202871811180415659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3618933603829081573887545 2714200202871811180415659)
                      ·
                        rfl

theorem cell23_5285886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 2, 1, 5, 2].length) (baseStart_5285886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5285886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5285886 prefixEnd_5285886 := by exact prefixLift 5285886
  have htrace : WordTrace (prefixWord ++ tailWord_5285886) baseStart_5285886 baseEnd_5285886 := by
    simpa [prefixWord, tailWord_5285886, baseEnd_5285886] using wordTrace_append hprefix tailTrace_5285886
  have hstable : (prefixWord ++ tailWord_5285886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5285886).length < 2 ^ (prefixWord ++ tailWord_5285886).sum := by decide
  have hdescent : baseEnd_5285886 < baseStart_5285886 := by decide
  rcases family_descends (prefixWord ++ tailWord_5285886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5285899 : List Nat := [1, 1, 1, 1, 6, 1, 4, 2, 1, 1, 4]
def baseStart_5285899 : Nat := 118140960795 + 5285899 * 2 ^ 59
def prefixEnd_5285899 : Nat := 4983230072969 + 3 ^ 40 * 5285899 * 2
def baseEnd_5285899 : Nat := 2714206878120319629553099

theorem tailTrace_5285899 : CollatzResearch.WordTrace tailWord_5285899 prefixEnd_5285899 2714206878120319629553099 := by
  unfold tailWord_5285899
  simp only [CollatzResearch.WordTrace]
  refine ⟨192792575077098157521940751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128528383384732105014627167 192792575077098157521940751)
  ·
    refine ⟨289188862615647236282911127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192792575077098157521940751 289188862615647236282911127)
    ·
      refine ⟨433783293923470854424366691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 289188862615647236282911127 433783293923470854424366691)
      ·
        refine ⟨650674940885206281636550037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 433783293923470854424366691 650674940885206281636550037)
        ·
          refine ⟨30500387853994044451713283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 650674940885206281636550037 30500387853994044451713283)
          ·
            refine ⟨45750581780991066677569925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30500387853994044451713283 45750581780991066677569925)
            ·
              refine ⟨8578234083935825002044361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45750581780991066677569925 8578234083935825002044361)
              ·
                refine ⟨6433675562951868751533271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8578234083935825002044361 6433675562951868751533271)
                ·
                  refine ⟨9650513344427803127299907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6433675562951868751533271 9650513344427803127299907)
                  ·
                    refine ⟨14475770016641704690949861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9650513344427803127299907 14475770016641704690949861)
                    ·
                      refine ⟨2714206878120319629553099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14475770016641704690949861 2714206878120319629553099)
                      ·
                        rfl

theorem cell23_5285899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 4, 2, 1, 1, 4].length) (baseStart_5285899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5285899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5285899 prefixEnd_5285899 := by exact prefixLift 5285899
  have htrace : WordTrace (prefixWord ++ tailWord_5285899) baseStart_5285899 baseEnd_5285899 := by
    simpa [prefixWord, tailWord_5285899, baseEnd_5285899] using wordTrace_append hprefix tailTrace_5285899
  have hstable : (prefixWord ++ tailWord_5285899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5285899).length < 2 ^ (prefixWord ++ tailWord_5285899).sum := by decide
  have hdescent : baseEnd_5285899 < baseStart_5285899 := by decide
  rcases family_descends (prefixWord ++ tailWord_5285899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5285902 : List Nat := [4, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5]
def baseStart_5285902 : Nat := 118140960795 + 5285902 * 2 ^ 59
def prefixEnd_5285902 : Nat := 4983230072969 + 3 ^ 40 * 5285902 * 2
def baseEnd_5285902 : Nat := 2714208418562283117815585

theorem tailTrace_5285902 : CollatzResearch.WordTrace tailWord_5285902 prefixEnd_5285902 2714208418562283117815585 := by
  unfold tailWord_5285902
  simp only [CollatzResearch.WordTrace]
  refine ⟨24099085562010911129287495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 128528456330724859356199973 24099085562010911129287495)
  ·
    refine ⟨36148628343016366693931243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24099085562010911129287495 36148628343016366693931243)
    ·
      refine ⟨54222942514524550040896865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36148628343016366693931243 54222942514524550040896865)
      ·
        refine ⟨40667206885893412530672649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54222942514524550040896865 40667206885893412530672649)
        ·
          refine ⟨30500405164420059398004487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40667206885893412530672649 30500405164420059398004487)
          ·
            refine ⟨45750607746630089097006731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30500405164420059398004487 45750607746630089097006731)
            ·
              refine ⟨68625911619945133645510097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45750607746630089097006731 68625911619945133645510097)
              ·
                refine ⟨51469433714958850234132573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68625911619945133645510097 51469433714958850234132573)
                ·
                  refine ⟨19301037643109568837799715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51469433714958850234132573 19301037643109568837799715)
                  ·
                    refine ⟨28951556464664353256699573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19301037643109568837799715 28951556464664353256699573)
                    ·
                      refine ⟨2714208418562283117815585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28951556464664353256699573 2714208418562283117815585)
                      ·
                        rfl

theorem cell23_5285902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5].length) (baseStart_5285902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5285902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5285902 prefixEnd_5285902 := by exact prefixLift 5285902
  have htrace : WordTrace (prefixWord ++ tailWord_5285902) baseStart_5285902 baseEnd_5285902 := by
    simpa [prefixWord, tailWord_5285902, baseEnd_5285902] using wordTrace_append hprefix tailTrace_5285902
  have hstable : (prefixWord ++ tailWord_5285902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5285902).length < 2 ^ (prefixWord ++ tailWord_5285902).sum := by decide
  have hdescent : baseEnd_5285902 < baseStart_5285902 := by decide
  rcases family_descends (prefixWord ++ tailWord_5285902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5285912 : List Nat := [2, 1, 2, 3, 2, 1, 2, 1, 3, 2, 4]
def baseStart_5285912 : Nat := 118140960795 + 5285912 * 2 ^ 59
def prefixEnd_5285912 : Nat := 4983230072969 + 3 ^ 40 * 5285912 * 2
def baseEnd_5285912 : Nat := 2714213553368828078690539

theorem tailTrace_5285912 : CollatzResearch.WordTrace tailWord_5285912 prefixEnd_5285912 2714213553368828078690539 := by
  unfold tailWord_5285912
  simp only [CollatzResearch.WordTrace]
  refine ⟨96396524613025530371081995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128528699484034040494775993 96396524613025530371081995)
  ·
    refine ⟨144594786919538295556622993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96396524613025530371081995 144594786919538295556622993)
    ·
      refine ⟨108446090189653721667467245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144594786919538295556622993 108446090189653721667467245)
      ·
        refine ⟨40667283821120145625300217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 108446090189653721667467245 40667283821120145625300217)
        ·
          refine ⟨30500462865840109218975163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40667283821120145625300217 30500462865840109218975163)
          ·
            refine ⟨45750694298760163828462745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30500462865840109218975163 45750694298760163828462745)
            ·
              refine ⟨34313020724070122871347059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45750694298760163828462745 34313020724070122871347059)
              ·
                refine ⟨51469531086105184307020589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34313020724070122871347059 51469531086105184307020589)
                ·
                  refine ⟨19301074157289444115132721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51469531086105184307020589 19301074157289444115132721)
                  ·
                    refine ⟨14475805617967083086349541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19301074157289444115132721 14475805617967083086349541)
                    ·
                      refine ⟨2714213553368828078690539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14475805617967083086349541 2714213553368828078690539)
                      ·
                        rfl

theorem cell23_5285912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 1, 3, 2, 4].length) (baseStart_5285912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5285912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5285912 prefixEnd_5285912 := by exact prefixLift 5285912
  have htrace : WordTrace (prefixWord ++ tailWord_5285912) baseStart_5285912 baseEnd_5285912 := by
    simpa [prefixWord, tailWord_5285912, baseEnd_5285912] using wordTrace_append hprefix tailTrace_5285912
  have hstable : (prefixWord ++ tailWord_5285912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5285912).length < 2 ^ (prefixWord ++ tailWord_5285912).sum := by decide
  have hdescent : baseEnd_5285912 < baseStart_5285912 := by decide
  rcases family_descends (prefixWord ++ tailWord_5285912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5285919 : List Nat := [1, 1, 2, 4, 1, 2, 1, 5, 1, 2, 3]
def baseStart_5285919 : Nat := 118140960795 + 5285919 * 2 ^ 59
def prefixEnd_5285919 : Nat := 4983230072969 + 3 ^ 40 * 5285919 * 2
def baseEnd_5285919 : Nat := 2714217147733409551303007

theorem tailTrace_5285919 : CollatzResearch.WordTrace tailWord_5285919 prefixEnd_5285919 2714217147733409551303007 := by
  unfold tailWord_5285919
  simp only [CollatzResearch.WordTrace]
  refine ⟨192793304537025700937668811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128528869691350467291779207 192793304537025700937668811)
  ·
    refine ⟨289189956805538551406503217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192793304537025700937668811 289189956805538551406503217)
    ·
      refine ⟨216892467604153913554877413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 289189956805538551406503217 216892467604153913554877413)
      ·
        refine ⟨40667337675778858791539515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 216892467604153913554877413 40667337675778858791539515)
        ·
          refine ⟨61001006513668288187309273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40667337675778858791539515 61001006513668288187309273)
          ·
            refine ⟨45750754885251216140481955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61001006513668288187309273 45750754885251216140481955)
            ·
              refine ⟨68626132327876824210722933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45750754885251216140481955 68626132327876824210722933)
              ·
                refine ⟨6433699905738452269755275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 68626132327876824210722933 6433699905738452269755275)
                ·
                  refine ⟨9650549858607678404632913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6433699905738452269755275 9650549858607678404632913)
                  ·
                    refine ⟨7237912393955758803474685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9650549858607678404632913 7237912393955758803474685)
                    ·
                      refine ⟨2714217147733409551303007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7237912393955758803474685 2714217147733409551303007)
                      ·
                        rfl

theorem cell23_5285919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 5, 1, 2, 3].length) (baseStart_5285919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5285919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5285919 prefixEnd_5285919 := by exact prefixLift 5285919
  have htrace : WordTrace (prefixWord ++ tailWord_5285919) baseStart_5285919 baseEnd_5285919 := by
    simpa [prefixWord, tailWord_5285919, baseEnd_5285919] using wordTrace_append hprefix tailTrace_5285919
  have hstable : (prefixWord ++ tailWord_5285919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5285919).length < 2 ^ (prefixWord ++ tailWord_5285919).sum := by decide
  have hdescent : baseEnd_5285919 < baseStart_5285919 := by decide
  rcases family_descends (prefixWord ++ tailWord_5285919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5285927 : List Nat := [1, 1, 7, 1, 2, 1, 3, 2, 1, 1, 3]
def baseStart_5285927 : Nat := 118140960795 + 5285927 * 2 ^ 59
def prefixEnd_5285927 : Nat := 4983230072969 + 3 ^ 40 * 5285927 * 2
def baseEnd_5285927 : Nat := 2714221255578645520002971

theorem tailTrace_5285927 : CollatzResearch.WordTrace tailWord_5285927 prefixEnd_5285927 2714221255578645520002971 := by
  unfold tailWord_5285927
  simp only [CollatzResearch.WordTrace]
  refine ⟨192793596320996718303960035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128529064213997812202640023 192793596320996718303960035)
  ·
    refine ⟨289190394481495077455940053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192793596320996718303960035 289190394481495077455940053)
    ·
      refine ⟨6777899870660040877873595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 289190394481495077455940053 6777899870660040877873595)
      ·
        refine ⟨10166849805990061316810393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6777899870660040877873595 10166849805990061316810393)
        ·
          refine ⟨7625137354492545987607795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10166849805990061316810393 7625137354492545987607795)
          ·
            refine ⟨11437706031738818981411693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7625137354492545987607795 11437706031738818981411693)
            ·
              refine ⟨4289139761902057118029385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11437706031738818981411693 4289139761902057118029385)
              ·
                refine ⟨3216854821426542838522039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4289139761902057118029385 3216854821426542838522039)
                ·
                  refine ⟨4825282232139814257783059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3216854821426542838522039 4825282232139814257783059)
                  ·
                    refine ⟨7237923348209721386674589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4825282232139814257783059 7237923348209721386674589)
                    ·
                      refine ⟨2714221255578645520002971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7237923348209721386674589 2714221255578645520002971)
                      ·
                        rfl

theorem cell23_5285927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 3, 2, 1, 1, 3].length) (baseStart_5285927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5285927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5285927 prefixEnd_5285927 := by exact prefixLift 5285927
  have htrace : WordTrace (prefixWord ++ tailWord_5285927) baseStart_5285927 baseEnd_5285927 := by
    simpa [prefixWord, tailWord_5285927, baseEnd_5285927] using wordTrace_append hprefix tailTrace_5285927
  have hstable : (prefixWord ++ tailWord_5285927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5285927).length < 2 ^ (prefixWord ++ tailWord_5285927).sum := by decide
  have hdescent : baseEnd_5285927 < baseStart_5285927 := by decide
  rcases family_descends (prefixWord ++ tailWord_5285927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5285932 : List Nat := [2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 3]
def baseStart_5285932 : Nat := 118140960795 + 5285932 * 2 ^ 59
def prefixEnd_5285932 : Nat := 4983230072969 + 3 ^ 40 * 5285932 * 2
def baseEnd_5285932 : Nat := 2714223822981918000440447

theorem tailTrace_5285932 : CollatzResearch.WordTrace tailWord_5285932 prefixEnd_5285932 2714223822981918000440447 := by
  unfold tailWord_5285932
  simp only [CollatzResearch.WordTrace]
  refine ⟨96396889342989302078946025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128529185790652402771928033 96396889342989302078946025)
  ·
    refine ⟨72297667007241976559209519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96396889342989302078946025 72297667007241976559209519)
    ·
      refine ⟨108446500510862964838814279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72297667007241976559209519 108446500510862964838814279)
      ·
        refine ⟨162669750766294447258221419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108446500510862964838814279 162669750766294447258221419)
        ·
          refine ⟨244004626149441670887332129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162669750766294447258221419 244004626149441670887332129)
          ·
            refine ⟨183003469612081253165499097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 244004626149441670887332129 183003469612081253165499097)
            ·
              refine ⟨137252602209060939874124323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 183003469612081253165499097 137252602209060939874124323)
              ·
                refine ⟨205878903313591409811186485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 137252602209060939874124323 205878903313591409811186485)
                ·
                  refine ⟨19301147185649194669798733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 205878903313591409811186485 19301147185649194669798733)
                  ·
                    refine ⟨7237930194618448001174525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19301147185649194669798733 7237930194618448001174525)
                    ·
                      refine ⟨2714223822981918000440447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7237930194618448001174525 2714223822981918000440447)
                      ·
                        rfl

theorem cell23_5285932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 3].length) (baseStart_5285932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5285932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5285932 prefixEnd_5285932 := by exact prefixLift 5285932
  have htrace : WordTrace (prefixWord ++ tailWord_5285932) baseStart_5285932 baseEnd_5285932 := by
    simpa [prefixWord, tailWord_5285932, baseEnd_5285932] using wordTrace_append hprefix tailTrace_5285932
  have hstable : (prefixWord ++ tailWord_5285932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5285932).length < 2 ^ (prefixWord ++ tailWord_5285932).sum := by decide
  have hdescent : baseEnd_5285932 < baseStart_5285932 := by decide
  rcases family_descends (prefixWord ++ tailWord_5285932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5285949 : List Nat := [1, 4, 1, 3, 1, 1, 2, 3, 1, 3, 3]
def baseStart_5285949 : Nat := 118140960795 + 5285949 * 2 ^ 59
def prefixEnd_5285949 : Nat := 4983230072969 + 3 ^ 40 * 5285949 * 2
def baseEnd_5285949 : Nat := 2714232552153044433927869

theorem tailTrace_5285949 : CollatzResearch.WordTrace tailWord_5285949 prefixEnd_5285949 2714232552153044433927869 := by
  unfold tailWord_5285949
  simp only [CollatzResearch.WordTrace]
  refine ⟨192794398726917016061260901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128529599151278010707507267 192794398726917016061260901)
  ·
    refine ⟨36148949761296940511486419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 192794398726917016061260901 36148949761296940511486419)
    ·
      refine ⟨54223424641945410767229629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36148949761296940511486419 54223424641945410767229629)
      ·
        refine ⟨20333784240729529037711111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54223424641945410767229629 20333784240729529037711111)
        ·
          refine ⟨30500676361094293556566667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20333784240729529037711111 30500676361094293556566667)
          ·
            refine ⟨45751014541641440334850001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30500676361094293556566667 45751014541641440334850001)
            ·
              refine ⟨34313260906231080251137501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45751014541641440334850001 34313260906231080251137501)
              ·
                refine ⟨12867472839836655094176563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34313260906231080251137501 12867472839836655094176563)
                ·
                  refine ⟨19301209259754982641264845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12867472839836655094176563 19301209259754982641264845)
                  ·
                    refine ⟨7237953472408118490474317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19301209259754982641264845 7237953472408118490474317)
                    ·
                      refine ⟨2714232552153044433927869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7237953472408118490474317 2714232552153044433927869)
                      ·
                        rfl

theorem cell23_5285949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 3, 1, 3, 3].length) (baseStart_5285949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5285949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5285949 prefixEnd_5285949 := by exact prefixLift 5285949
  have htrace : WordTrace (prefixWord ++ tailWord_5285949) baseStart_5285949 baseEnd_5285949 := by
    simpa [prefixWord, tailWord_5285949, baseEnd_5285949] using wordTrace_append hprefix tailTrace_5285949
  have hstable : (prefixWord ++ tailWord_5285949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5285949).length < 2 ^ (prefixWord ++ tailWord_5285949).sum := by decide
  have hdescent : baseEnd_5285949 < baseStart_5285949 := by decide
  rcases family_descends (prefixWord ++ tailWord_5285949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5285950 : List Nat := [4, 2, 1, 3, 3, 1, 1, 2, 1, 1, 4]
def baseStart_5285950 : Nat := 118140960795 + 5285950 * 2 ^ 59
def prefixEnd_5285950 : Nat := 4983230072969 + 3 ^ 40 * 5285950 * 2
def baseEnd_5285950 : Nat := 2714233065633698930015365

theorem tailTrace_5285950 : CollatzResearch.WordTrace tailWord_5285950 prefixEnd_5285950 2714233065633698930015365 := by
  unfold tailWord_5285950
  simp only [CollatzResearch.WordTrace]
  refine ⟨24099304399989174154005913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 128529623466608928821364869 24099304399989174154005913)
  ·
    refine ⟨18074478299991880615504435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24099304399989174154005913 18074478299991880615504435)
    ·
      refine ⟨27111717449987820923256653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18074478299991880615504435 27111717449987820923256653)
      ·
        refine ⟨10166894043745432846221245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27111717449987820923256653 10166894043745432846221245)
        ·
          refine ⟨3812585266404537317332967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10166894043745432846221245 3812585266404537317332967)
          ·
            refine ⟨5718877899606805975999451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3812585266404537317332967 5718877899606805975999451)
            ·
              refine ⟨8578316849410208963999177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5718877899606805975999451 8578316849410208963999177)
              ·
                refine ⟨6433737637057656722999383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8578316849410208963999177 6433737637057656722999383)
                ·
                  refine ⟨9650606455586485084499075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6433737637057656722999383 9650606455586485084499075)
                  ·
                    refine ⟨14475909683379727626748613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9650606455586485084499075 14475909683379727626748613)
                    ·
                      refine ⟨2714233065633698930015365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14475909683379727626748613 2714233065633698930015365)
                      ·
                        rfl

theorem cell23_5285950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 1, 2, 1, 1, 4].length) (baseStart_5285950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5285950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5285950 prefixEnd_5285950 := by exact prefixLift 5285950
  have htrace : WordTrace (prefixWord ++ tailWord_5285950) baseStart_5285950 baseEnd_5285950 := by
    simpa [prefixWord, tailWord_5285950, baseEnd_5285950] using wordTrace_append hprefix tailTrace_5285950
  have hstable : (prefixWord ++ tailWord_5285950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5285950).length < 2 ^ (prefixWord ++ tailWord_5285950).sum := by decide
  have hdescent : baseEnd_5285950 < baseStart_5285950 := by decide
  rcases family_descends (prefixWord ++ tailWord_5285950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5285953 : List Nat := [1, 2, 5, 1, 2, 3, 1, 2, 1, 2, 3]
def baseStart_5285953 : Nat := 118140960795 + 5285953 * 2 ^ 59
def prefixEnd_5285953 : Nat := 4983230072969 + 3 ^ 40 * 5285953 * 2
def baseEnd_5285953 : Nat := 2714234606075662418277851

theorem tailTrace_5285953 : CollatzResearch.WordTrace tailWord_5285953 prefixEnd_5285953 2714234606075662418277851 := by
  unfold tailWord_5285953
  simp only [CollatzResearch.WordTrace]
  refine ⟨192794544618902524744406513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128529696412601683162937675 192794544618902524744406513)
  ·
    refine ⟨144595908464176893558304885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192794544618902524744406513 144595908464176893558304885)
    ·
      refine ⟨13555866418516583771091083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 144595908464176893558304885 13555866418516583771091083)
      ·
        refine ⟨20333799627774875656636625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13555866418516583771091083 20333799627774875656636625)
        ·
          refine ⟨15250349720831156742477469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20333799627774875656636625 15250349720831156742477469)
          ·
            refine ⟨5718881145311683778429051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15250349720831156742477469 5718881145311683778429051)
            ·
              refine ⟨8578321717967525667643577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5718881145311683778429051 8578321717967525667643577)
              ·
                refine ⟨6433741288475644250732683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8578321717967525667643577 6433741288475644250732683)
                ·
                  refine ⟨9650611932713466376099025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6433741288475644250732683 9650611932713466376099025)
                  ·
                    refine ⟨7237958949535099782074269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9650611932713466376099025 7237958949535099782074269)
                    ·
                      refine ⟨2714234606075662418277851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7237958949535099782074269 2714234606075662418277851)
                      ·
                        rfl

theorem cell23_5285953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 1, 2, 1, 2, 3].length) (baseStart_5285953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5285953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5285953 prefixEnd_5285953 := by exact prefixLift 5285953
  have htrace : WordTrace (prefixWord ++ tailWord_5285953) baseStart_5285953 baseEnd_5285953 := by
    simpa [prefixWord, tailWord_5285953, baseEnd_5285953] using wordTrace_append hprefix tailTrace_5285953
  have hstable : (prefixWord ++ tailWord_5285953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5285953).length < 2 ^ (prefixWord ++ tailWord_5285953).sum := by decide
  have hdescent : baseEnd_5285953 < baseStart_5285953 := by decide
  rcases family_descends (prefixWord ++ tailWord_5285953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5286012 : List Nat := [2, 2, 2, 1, 1, 4, 1, 1, 9]
def baseStart_5286012 : Nat := 118140960795 + 5286012 * 2 ^ 59
def prefixEnd_5286012 : Nat := 4983230072969 + 3 ^ 40 * 5286012 * 2
def baseEnd_5286012 : Nat := 301584989048253076382231

theorem tailTrace_5286012 : CollatzResearch.WordTrace tailWord_5286012 prefixEnd_5286012 301584989048253076382231 := by
  unfold tailWord_5286012
  simp only [CollatzResearch.WordTrace]
  refine ⟨96398348262844388910402145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128531131017125851880536193 96398348262844388910402145)
  ·
    refine ⟨72298761197133291682801609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96398348262844388910402145 72298761197133291682801609)
    ·
      refine ⟨54224070897849968762101207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72298761197133291682801609 54224070897849968762101207)
      ·
        refine ⟨81336106346774953143151811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54224070897849968762101207 81336106346774953143151811)
        ·
          refine ⟨122004159520162429714727717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81336106346774953143151811 122004159520162429714727717)
          ·
            refine ⟨22875779910030455571511447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 122004159520162429714727717 22875779910030455571511447)
            ·
              refine ⟨34313669865045683357267171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22875779910030455571511447 34313669865045683357267171)
              ·
                refine ⟨51470504797568525035900757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34313669865045683357267171 51470504797568525035900757)
                ·
                  refine ⟨301584989048253076382231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 51470504797568525035900757 301584989048253076382231)
                  ·
                    rfl

theorem cell23_5286012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 1, 9].length) (baseStart_5286012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5286012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5286012 prefixEnd_5286012 := by exact prefixLift 5286012
  have htrace : WordTrace (prefixWord ++ tailWord_5286012) baseStart_5286012 baseEnd_5286012 := by
    simpa [prefixWord, tailWord_5286012, baseEnd_5286012] using wordTrace_append hprefix tailTrace_5286012
  have hstable : (prefixWord ++ tailWord_5286012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5286012).length < 2 ^ (prefixWord ++ tailWord_5286012).sum := by decide
  have hdescent : baseEnd_5286012 < baseStart_5286012 := by decide
  rcases family_descends (prefixWord ++ tailWord_5286012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5286072 : List Nat := [2, 1, 2, 1, 2, 1, 3, 1, 2, 8]
def baseStart_5286072 : Nat := 118140960795 + 5286072 * 2 ^ 59
def prefixEnd_5286072 : Nat := 4983230072969 + 3 ^ 40 * 5286072 * 2
def baseEnd_5286072 : Nat := 904765236757849150896601

theorem tailTrace_5286072 : CollatzResearch.WordTrace tailWord_5286072 prefixEnd_5286072 904765236757849150896601 := by
  unfold tailWord_5286072
  simp only [CollatzResearch.WordTrace]
  refine ⟨96399442452735704033994235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128532589936980938711992313 96399442452735704033994235)
  ·
    refine ⟨144599163679103556050991353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96399442452735704033994235 144599163679103556050991353)
    ·
      refine ⟨108449372759327667038243515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144599163679103556050991353 108449372759327667038243515)
      ·
        refine ⟨162674059138991500557365273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108449372759327667038243515 162674059138991500557365273)
        ·
          refine ⟨122005544354243625418023955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 162674059138991500557365273 122005544354243625418023955)
          ·
            refine ⟨183008316531365438127035933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122005544354243625418023955 183008316531365438127035933)
            ·
              refine ⟨68628118699262039297638475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 183008316531365438127035933 68628118699262039297638475)
              ·
                refine ⟨102942178048893058946457713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68628118699262039297638475 102942178048893058946457713)
                ·
                  refine ⟨77206633536669794209843285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 102942178048893058946457713 77206633536669794209843285)
                  ·
                    refine ⟨904765236757849150896601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 77206633536669794209843285 904765236757849150896601)
                    ·
                      rfl

theorem cell23_5286072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 1, 2, 8].length) (baseStart_5286072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5286072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5286072 prefixEnd_5286072 := by exact prefixLift 5286072
  have htrace : WordTrace (prefixWord ++ tailWord_5286072) baseStart_5286072 baseEnd_5286072 := by
    simpa [prefixWord, tailWord_5286072, baseEnd_5286072] using wordTrace_append hprefix tailTrace_5286072
  have hstable : (prefixWord ++ tailWord_5286072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5286072).length < 2 ^ (prefixWord ++ tailWord_5286072).sum := by decide
  have hdescent : baseEnd_5286072 < baseStart_5286072 := by decide
  rcases family_descends (prefixWord ++ tailWord_5286072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5286079 : List Nat := [1, 1, 2, 2, 2, 2, 1, 5, 2, 1, 4]
def baseStart_5286079 : Nat := 118140960795 + 5286079 * 2 ^ 59
def prefixEnd_5286079 : Nat := 4983230072969 + 3 ^ 40 * 5286079 * 2
def baseEnd_5286079 : Nat := 2714299304638128925302271

theorem tailTrace_5286079 : CollatzResearch.WordTrace tailWord_5286079 prefixEnd_5286079 2714299304638128925302271 := by
  unfold tailWord_5286079
  simp only [CollatzResearch.WordTrace]
  refine ⟨192799140216446048263493291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128532760144297365508995527 192799140216446048263493291)
  ·
    refine ⟨289198710324669072395239937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192799140216446048263493291 289198710324669072395239937)
    ·
      refine ⟨216899032743501804296429953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 289198710324669072395239937 216899032743501804296429953)
      ·
        refine ⟨162674274557626353222322465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 216899032743501804296429953 162674274557626353222322465)
        ·
          refine ⟨122005705918219764916741849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 162674274557626353222322465 122005705918219764916741849)
          ·
            refine ⟨91504279438664823687556387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 122005705918219764916741849 91504279438664823687556387)
            ·
              refine ⟨137256419157997235531334581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91504279438664823687556387 137256419157997235531334581)
              ·
                refine ⟨12867789296062240831062617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 137256419157997235531334581 12867789296062240831062617)
                ·
                  refine ⟨9650841972046680623296963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12867789296062240831062617 9650841972046680623296963)
                  ·
                    refine ⟨14476262958070020934945445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9650841972046680623296963 14476262958070020934945445)
                    ·
                      refine ⟨2714299304638128925302271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14476262958070020934945445 2714299304638128925302271)
                      ·
                        rfl

theorem cell23_5286079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 5, 2, 1, 4].length) (baseStart_5286079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5286079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5286079 prefixEnd_5286079 := by exact prefixLift 5286079
  have htrace : WordTrace (prefixWord ++ tailWord_5286079) baseStart_5286079 baseEnd_5286079 := by
    simpa [prefixWord, tailWord_5286079, baseEnd_5286079] using wordTrace_append hprefix tailTrace_5286079
  have hstable : (prefixWord ++ tailWord_5286079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5286079).length < 2 ^ (prefixWord ++ tailWord_5286079).sum := by decide
  have hdescent : baseEnd_5286079 < baseStart_5286079 := by decide
  rcases family_descends (prefixWord ++ tailWord_5286079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5286106 : List Nat := [3, 1, 1, 2, 2, 1, 5, 1, 3, 4]
def baseStart_5286106 : Nat := 118140960795 + 5286106 * 2 ^ 59
def prefixEnd_5286106 : Nat := 4983230072969 + 3 ^ 40 * 5286106 * 2
def baseEnd_5286106 : Nat := 904771056205266773221549

theorem tailTrace_5286106 : CollatzResearch.WordTrace tailWord_5286106 prefixEnd_5286106 904771056205266773221549 := by
  unfold tailWord_5286106
  simp only [CollatzResearch.WordTrace]
  refine ⟨48200031246837057968681543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128533416658232154583150781 48200031246837057968681543)
  ·
    refine ⟨72300046870255586953022315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48200031246837057968681543 72300046870255586953022315)
    ·
      refine ⟨108450070305383380429533473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72300046870255586953022315 108450070305383380429533473)
      ·
        refine ⟨81337552729037535322150105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108450070305383380429533473 81337552729037535322150105)
        ·
          refine ⟨61003164546778151491612579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81337552729037535322150105 61003164546778151491612579)
          ·
            refine ⟨91504746820167227237418869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61003164546778151491612579 91504746820167227237418869)
            ·
              refine ⟨8578570014390677553508019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 91504746820167227237418869 8578570014390677553508019)
              ·
                refine ⟨12867855021586016330262029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8578570014390677553508019 12867855021586016330262029)
                ·
                  refine ⟨4825445633094756123848261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12867855021586016330262029 4825445633094756123848261)
                  ·
                    refine ⟨904771056205266773221549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4825445633094756123848261 904771056205266773221549)
                    ·
                      rfl

theorem cell23_5286106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 5, 1, 3, 4].length) (baseStart_5286106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5286106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5286106 prefixEnd_5286106 := by exact prefixLift 5286106
  have htrace : WordTrace (prefixWord ++ tailWord_5286106) baseStart_5286106 baseEnd_5286106 := by
    simpa [prefixWord, tailWord_5286106, baseEnd_5286106] using wordTrace_append hprefix tailTrace_5286106
  have hstable : (prefixWord ++ tailWord_5286106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5286106).length < 2 ^ (prefixWord ++ tailWord_5286106).sum := by decide
  have hdescent : baseEnd_5286106 < baseStart_5286106 := by decide
  rcases family_descends (prefixWord ++ tailWord_5286106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5286129 : List Nat := [1, 2, 2, 2, 2, 1, 2, 1, 2, 5, 3]
def baseStart_5286129 : Nat := 118140960795 + 5286129 * 2 ^ 59
def prefixEnd_5286129 : Nat := 4983230072969 + 3 ^ 40 * 5286129 * 2
def baseEnd_5286129 : Nat := 2714324978670853729677041

theorem tailTrace_5286129 : CollatzResearch.WordTrace tailWord_5286129 prefixEnd_5286129 2714324978670853729677041 := by
  unfold tailWord_5286129
  simp only [CollatzResearch.WordTrace]
  refine ⟨192800963866264906802813441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128533975910843271201875627 192800963866264906802813441)
  ·
    refine ⟨144600722899698680102110081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192800963866264906802813441 144600722899698680102110081)
    ·
      refine ⟨108450542174774010076582561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144600722899698680102110081 108450542174774010076582561)
      ·
        refine ⟨81337906631080507557436921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108450542174774010076582561 81337906631080507557436921)
        ·
          refine ⟨61003429973310380668077691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81337906631080507557436921 61003429973310380668077691)
          ·
            refine ⟨91505144959965571002116537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61003429973310380668077691 91505144959965571002116537)
            ·
              refine ⟨68628858719974178251587403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91505144959965571002116537 68628858719974178251587403)
              ·
                refine ⟨102943288079961267377381105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68628858719974178251587403 102943288079961267377381105)
                ·
                  refine ⟨77207466059970950533035829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 102943288079961267377381105 77207466059970950533035829)
                  ·
                    refine ⟨7238199943122276612472109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 77207466059970950533035829 7238199943122276612472109)
                    ·
                      refine ⟨2714324978670853729677041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7238199943122276612472109 2714324978670853729677041)
                      ·
                        rfl

theorem cell23_5286129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 1, 2, 5, 3].length) (baseStart_5286129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5286129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5286129 prefixEnd_5286129 := by exact prefixLift 5286129
  have htrace : WordTrace (prefixWord ++ tailWord_5286129) baseStart_5286129 baseEnd_5286129 := by
    simpa [prefixWord, tailWord_5286129, baseEnd_5286129] using wordTrace_append hprefix tailTrace_5286129
  have hstable : (prefixWord ++ tailWord_5286129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5286129).length < 2 ^ (prefixWord ++ tailWord_5286129).sum := by decide
  have hdescent : baseEnd_5286129 < baseStart_5286129 := by decide
  rcases family_descends (prefixWord ++ tailWord_5286129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5286220 : List Nat := [2, 2, 1, 3, 2, 1, 4, 1, 3, 2, 2]
def baseStart_5286220 : Nat := 118140960795 + 5286220 * 2 ^ 59
def prefixEnd_5286220 : Nat := 4983230072969 + 3 ^ 40 * 5286220 * 2
def baseEnd_5286220 : Nat := 2714371705410412873639123

theorem tailTrace_5286220 : CollatzResearch.WordTrace tailWord_5286220 prefixEnd_5286220 2714371705410412873639123 := by
  unfold tailWord_5286220
  simp only [CollatzResearch.WordTrace]
  refine ⟨96402141454467614672188057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128536188605956819562917409 96402141454467614672188057)
  ·
    refine ⟨72301606090850711004141043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96402141454467614672188057 72301606090850711004141043)
    ·
      refine ⟨108452409136276066506211565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72301606090850711004141043 108452409136276066506211565)
      ·
        refine ⟨40669653426103524939829337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 108452409136276066506211565 40669653426103524939829337)
        ·
          refine ⟨30502240069577643704872003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40669653426103524939829337 30502240069577643704872003)
          ·
            refine ⟨45753360104366465557308005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30502240069577643704872003 45753360104366465557308005)
            ·
              refine ⟨8578755019568712291995251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45753360104366465557308005 8578755019568712291995251)
              ·
                refine ⟨12868132529353068437992877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8578755019568712291995251 12868132529353068437992877)
                ·
                  refine ⟨4825549698507400664247329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12868132529353068437992877 4825549698507400664247329)
                  ·
                    refine ⟨3619162273880550498185497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4825549698507400664247329 3619162273880550498185497)
                    ·
                      refine ⟨2714371705410412873639123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3619162273880550498185497 2714371705410412873639123)
                      ·
                        rfl

theorem cell23_5286220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 4, 1, 3, 2, 2].length) (baseStart_5286220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5286220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5286220 prefixEnd_5286220 := by exact prefixLift 5286220
  have htrace : WordTrace (prefixWord ++ tailWord_5286220) baseStart_5286220 baseEnd_5286220 := by
    simpa [prefixWord, tailWord_5286220, baseEnd_5286220] using wordTrace_append hprefix tailTrace_5286220
  have hstable : (prefixWord ++ tailWord_5286220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5286220).length < 2 ^ (prefixWord ++ tailWord_5286220).sum := by decide
  have hdescent : baseEnd_5286220 < baseStart_5286220 := by decide
  rcases family_descends (prefixWord ++ tailWord_5286220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5286239 : List Nat := [1, 1, 2, 3, 1, 2, 2, 2, 2, 7]
def baseStart_5286239 : Nat := 118140960795 + 5286239 * 2 ^ 59
def prefixEnd_5286239 : Nat := 4983230072969 + 3 ^ 40 * 5286239 * 2
def baseEnd_5286239 : Nat := 904793820514282766433845

theorem tailTrace_5286239 : CollatzResearch.WordTrace tailWord_5286239 prefixEnd_5286239 904793820514282766433845 := by
  unfold tailWord_5286239
  simp only [CollatzResearch.WordTrace]
  refine ⟨192804975895866395589317771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128536650597244263726211847 192804975895866395589317771)
  ·
    refine ⟨289207463843799593383976657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192804975895866395589317771 289207463843799593383976657)
    ·
      refine ⟨216905597882849695037982493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 289207463843799593383976657 216905597882849695037982493)
      ·
        refine ⟨81339599206068635639243435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 216905597882849695037982493 81339599206068635639243435)
        ·
          refine ⟨122009398809102953458865153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81339599206068635639243435 122009398809102953458865153)
          ·
            refine ⟨91507049106827215094148865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 122009398809102953458865153 91507049106827215094148865)
            ·
              refine ⟨68630286830120411320611649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91507049106827215094148865 68630286830120411320611649)
              ·
                refine ⟨51472715122590308490458737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68630286830120411320611649 51472715122590308490458737)
                ·
                  refine ⟨38604536341942731367844053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51472715122590308490458737 38604536341942731367844053)
                  ·
                    refine ⟨904793820514282766433845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38604536341942731367844053 904793820514282766433845)
                    ·
                      rfl

theorem cell23_5286239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 2, 2, 7].length) (baseStart_5286239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5286239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5286239 prefixEnd_5286239 := by exact prefixLift 5286239
  have htrace : WordTrace (prefixWord ++ tailWord_5286239) baseStart_5286239 baseEnd_5286239 := by
    simpa [prefixWord, tailWord_5286239, baseEnd_5286239] using wordTrace_append hprefix tailTrace_5286239
  have hstable : (prefixWord ++ tailWord_5286239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5286239).length < 2 ^ (prefixWord ++ tailWord_5286239).sum := by decide
  have hdescent : baseEnd_5286239 < baseStart_5286239 := by decide
  rcases family_descends (prefixWord ++ tailWord_5286239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5286240 : List Nat := [2, 1, 1, 3, 5, 1, 2, 2, 1, 2, 3]
def baseStart_5286240 : Nat := 118140960795 + 5286240 * 2 ^ 59
def prefixEnd_5286240 : Nat := 4983230072969 + 3 ^ 40 * 5286240 * 2
def baseEnd_5286240 : Nat := 2714381975023502795389031

theorem tailTrace_5286240 : CollatzResearch.WordTrace tailWord_5286240 prefixEnd_5286240 2714381975023502795389031 := by
  unfold tailWord_5286240
  simp only [CollatzResearch.WordTrace]
  refine ⟨96402506184431386380052087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128536674912575181840069449 96402506184431386380052087)
  ·
    refine ⟨144603759276647079570078131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96402506184431386380052087 144603759276647079570078131)
    ·
      refine ⟨216905638914970619355117197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144603759276647079570078131 216905638914970619355117197)
      ·
        refine ⟨81339614593113982258168949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 216905638914970619355117197 81339614593113982258168949)
        ·
          refine ⟨7625588868104435836703339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 81339614593113982258168949 7625588868104435836703339)
          ·
            refine ⟨11438383302156653755055009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7625588868104435836703339 11438383302156653755055009)
            ·
              refine ⟨8578787476617490316291257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11438383302156653755055009 8578787476617490316291257)
              ·
                refine ⟨6434090607463117737218443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8578787476617490316291257 6434090607463117737218443)
                ·
                  refine ⟨9651135911194676605827665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6434090607463117737218443 9651135911194676605827665)
                  ·
                    refine ⟨7238351933396007454370749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9651135911194676605827665 7238351933396007454370749)
                    ·
                      refine ⟨2714381975023502795389031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7238351933396007454370749 2714381975023502795389031)
                      ·
                        rfl

theorem cell23_5286240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 2, 2, 1, 2, 3].length) (baseStart_5286240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5286240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5286240 prefixEnd_5286240 := by exact prefixLift 5286240
  have htrace : WordTrace (prefixWord ++ tailWord_5286240) baseStart_5286240 baseEnd_5286240 := by
    simpa [prefixWord, tailWord_5286240, baseEnd_5286240] using wordTrace_append hprefix tailTrace_5286240
  have hstable : (prefixWord ++ tailWord_5286240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5286240).length < 2 ^ (prefixWord ++ tailWord_5286240).sum := by decide
  have hdescent : baseEnd_5286240 < baseStart_5286240 := by decide
  rcases family_descends (prefixWord ++ tailWord_5286240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5286249 : List Nat := [1, 2, 1, 1, 1, 3, 3, 1, 1, 4, 5]
def baseStart_5286249 : Nat := 118140960795 + 5286249 * 2 ^ 59
def prefixEnd_5286249 : Nat := 4983230072969 + 3 ^ 40 * 5286249 * 2
def baseEnd_5286249 : Nat := 2714386596349393260176489

theorem tailTrace_5286249 : CollatzResearch.WordTrace tailWord_5286249 prefixEnd_5286249 2714386596349393260176489 := by
  unfold tailWord_5286249
  simp only [CollatzResearch.WordTrace]
  refine ⟨192805340625830167297181801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128536893750553444864787867 192805340625830167297181801)
  ·
    refine ⟨144604005469372625472886351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192805340625830167297181801 144604005469372625472886351)
    ·
      refine ⟨216906008204058938209329527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144604005469372625472886351 216906008204058938209329527)
      ·
        refine ⟨325359012306088407313994291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 216906008204058938209329527 325359012306088407313994291)
        ·
          refine ⟨488038518459132610970991437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 325359012306088407313994291 488038518459132610970991437)
          ·
            refine ⟨183014444422174729114121789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 488038518459132610970991437 183014444422174729114121789)
            ·
              refine ⟨68630416658315523417795671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 183014444422174729114121789 68630416658315523417795671)
              ·
                refine ⟨102945624987473285126693507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68630416658315523417795671 102945624987473285126693507)
                ·
                  refine ⟨154418437481209927690040261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 102945624987473285126693507 154418437481209927690040261)
                  ·
                    refine ⟨28953457027726861441882549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 154418437481209927690040261 28953457027726861441882549)
                    ·
                      refine ⟨2714386596349393260176489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28953457027726861441882549 2714386596349393260176489)
                      ·
                        rfl

theorem cell23_5286249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 1, 1, 4, 5].length) (baseStart_5286249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5286249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5286249 prefixEnd_5286249 := by exact prefixLift 5286249
  have htrace : WordTrace (prefixWord ++ tailWord_5286249) baseStart_5286249 baseEnd_5286249 := by
    simpa [prefixWord, tailWord_5286249, baseEnd_5286249] using wordTrace_append hprefix tailTrace_5286249
  have hstable : (prefixWord ++ tailWord_5286249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5286249).length < 2 ^ (prefixWord ++ tailWord_5286249).sum := by decide
  have hdescent : baseEnd_5286249 < baseStart_5286249 := by decide
  rcases family_descends (prefixWord ++ tailWord_5286249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5286253 : List Nat := [1, 5, 1, 1, 1, 2, 1, 1, 6, 1, 3]
def baseStart_5286253 : Nat := 118140960795 + 5286253 * 2 ^ 59
def prefixEnd_5286253 : Nat := 4983230072969 + 3 ^ 40 * 5286253 * 2
def baseEnd_5286253 : Nat := 2714388650272011244526471

theorem tailTrace_5286253 : CollatzResearch.WordTrace tailWord_5286253 prefixEnd_5286253 2714388650272011244526471 := by
  unfold tailWord_5286253
  simp only [CollatzResearch.WordTrace]
  refine ⟨192805486517815675980327413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128536991011877117320218275 192805486517815675980327413)
  ·
    refine ⟨18075514361045219623155695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 192805486517815675980327413 18075514361045219623155695)
    ·
      refine ⟨27113271541567829434733543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18075514361045219623155695 27113271541567829434733543)
      ·
        refine ⟨40669907312351744152100315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27113271541567829434733543 40669907312351744152100315)
        ·
          refine ⟨61004860968527616228150473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40669907312351744152100315 61004860968527616228150473)
          ·
            refine ⟨45753645726395712171112855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61004860968527616228150473 45753645726395712171112855)
            ·
              refine ⟨68630468589593568256669283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45753645726395712171112855 68630468589593568256669283)
              ·
                refine ⟨102945702884390352385003925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68630468589593568256669283 102945702884390352385003925)
                ·
                  refine ⟨4825579822705797768047059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 102945702884390352385003925 4825579822705797768047059)
                  ·
                    refine ⟨7238369734058696652070589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4825579822705797768047059 7238369734058696652070589)
                    ·
                      refine ⟨2714388650272011244526471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7238369734058696652070589 2714388650272011244526471)
                      ·
                        rfl

theorem cell23_5286253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 1, 6, 1, 3].length) (baseStart_5286253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5286253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5286253 prefixEnd_5286253 := by exact prefixLift 5286253
  have htrace : WordTrace (prefixWord ++ tailWord_5286253) baseStart_5286253 baseEnd_5286253 := by
    simpa [prefixWord, tailWord_5286253, baseEnd_5286253] using wordTrace_append hprefix tailTrace_5286253
  have hstable : (prefixWord ++ tailWord_5286253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5286253).length < 2 ^ (prefixWord ++ tailWord_5286253).sum := by decide
  have hdescent : baseEnd_5286253 < baseStart_5286253 := by decide
  rcases family_descends (prefixWord ++ tailWord_5286253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5286276 : List Nat := [2, 3, 2, 1, 1, 2, 2, 1, 2, 3, 4]
def baseStart_5286276 : Nat := 118140960795 + 5286276 * 2 ^ 59
def prefixEnd_5286276 : Nat := 4983230072969 + 3 ^ 40 * 5286276 * 2
def baseEnd_5286276 : Nat := 2714400460327064654538865

theorem tailTrace_5286276 : CollatzResearch.WordTrace tailWord_5286276 prefixEnd_5286276 2714400460327064654538865 := by
  unfold tailWord_5286276
  simp only [CollatzResearch.WordTrace]
  refine ⟨96403162698366175454207341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128537550264488233938943121 96403162698366175454207341)
  ·
    refine ⟨36151186011887315795327753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96403162698366175454207341 36151186011887315795327753)
    ·
      refine ⟨27113389508915486846495815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36151186011887315795327753 27113389508915486846495815)
      ·
        refine ⟨40670084263373230269743723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27113389508915486846495815 40670084263373230269743723)
        ·
          refine ⟨61005126395059845404615585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40670084263373230269743723 61005126395059845404615585)
          ·
            refine ⟨45753844796294884053461689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61005126395059845404615585 45753844796294884053461689)
            ·
              refine ⟨34315383597221163040096267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45753844796294884053461689 34315383597221163040096267)
              ·
                refine ⟨51473075395831744560144401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34315383597221163040096267 51473075395831744560144401)
                ·
                  refine ⟨38604806546873808420108301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51473075395831744560144401 38604806546873808420108301)
                  ·
                    refine ⟨14476802455077678157540613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 38604806546873808420108301 14476802455077678157540613)
                    ·
                      refine ⟨2714400460327064654538865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14476802455077678157540613 2714400460327064654538865)
                      ·
                        rfl

theorem cell23_5286276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 1, 2, 3, 4].length) (baseStart_5286276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5286276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5286276 prefixEnd_5286276 := by exact prefixLift 5286276
  have htrace : WordTrace (prefixWord ++ tailWord_5286276) baseStart_5286276 baseEnd_5286276 := by
    simpa [prefixWord, tailWord_5286276, baseEnd_5286276] using wordTrace_append hprefix tailTrace_5286276
  have hstable : (prefixWord ++ tailWord_5286276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5286276).length < 2 ^ (prefixWord ++ tailWord_5286276).sum := by decide
  have hdescent : baseEnd_5286276 < baseStart_5286276 := by decide
  rcases family_descends (prefixWord ++ tailWord_5286276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5286293 : List Nat := [1, 3, 2, 1, 1, 2, 1, 5, 1, 4, 2]
def baseStart_5286293 : Nat := 118140960795 + 5286293 * 2 ^ 59
def prefixEnd_5286293 : Nat := 4983230072969 + 3 ^ 40 * 5286293 * 2
def baseEnd_5286293 : Nat := 2714409189498191088026287

theorem tailTrace_5286293 : CollatzResearch.WordTrace tailWord_5286293 prefixEnd_5286293 2714409189498191088026287 := by
  unfold tailWord_5286293
  simp only [CollatzResearch.WordTrace]
  refine ⟨192806945437670762811783533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128537963625113841874522355 192806945437670762811783533)
  ·
    refine ⟨72302604539126536054418825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 192806945437670762811783533 72302604539126536054418825)
    ·
      refine ⟨54226953404344902040814119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72302604539126536054418825 54226953404344902040814119)
      ·
        refine ⟨81340430106517353061221179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54226953404344902040814119 81340430106517353061221179)
        ·
          refine ⟨122010645159776029591831769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81340430106517353061221179 122010645159776029591831769)
          ·
            refine ⟨91507983869832022193873827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 122010645159776029591831769 91507983869832022193873827)
            ·
              refine ⟨137261975804748033290810741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91507983869832022193873827 137261975804748033290810741)
              ·
                refine ⟨12868310231695128121013507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 137261975804748033290810741 12868310231695128121013507)
                ·
                  refine ⟨19302465347542692181520261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12868310231695128121013507 19302465347542692181520261)
                  ·
                    refine ⟨3619212252664254784035049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19302465347542692181520261 3619212252664254784035049)
                    ·
                      refine ⟨2714409189498191088026287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3619212252664254784035049 2714409189498191088026287)
                      ·
                        rfl

theorem cell23_5286293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 5, 1, 4, 2].length) (baseStart_5286293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5286293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5286293 prefixEnd_5286293 := by exact prefixLift 5286293
  have htrace : WordTrace (prefixWord ++ tailWord_5286293) baseStart_5286293 baseEnd_5286293 := by
    simpa [prefixWord, tailWord_5286293, baseEnd_5286293] using wordTrace_append hprefix tailTrace_5286293
  have hstable : (prefixWord ++ tailWord_5286293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5286293).length < 2 ^ (prefixWord ++ tailWord_5286293).sum := by decide
  have hdescent : baseEnd_5286293 < baseStart_5286293 := by decide
  rcases family_descends (prefixWord ++ tailWord_5286293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5286327 : List Nat := [1, 1, 3, 1, 3, 4, 2, 2, 2, 2, 2]
def baseStart_5286327 : Nat := 118140960795 + 5286327 * 2 ^ 59
def prefixEnd_5286327 : Nat := 4983230072969 + 3 ^ 40 * 5286327 * 2
def baseEnd_5286327 : Nat := 2714426647840443955001131

theorem tailTrace_5286327 : CollatzResearch.WordTrace tailWord_5286327 prefixEnd_5286327 2714426647840443955001131 := by
  unfold tailWord_5286327
  simp only [CollatzResearch.WordTrace]
  refine ⟨192808185519547586618521235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128538790346365057745680823 192808185519547586618521235)
  ·
    refine ⟨289212278279321379927781853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192808185519547586618521235 289212278279321379927781853)
    ·
      refine ⟨108454604354745517472918195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 289212278279321379927781853 108454604354745517472918195)
      ·
        refine ⟨162681906532118276209377293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108454604354745517472918195 162681906532118276209377293)
        ·
          refine ⟨61005714949544353578516485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 162681906532118276209377293 61005714949544353578516485)
          ·
            refine ⟨11438571553039566295971841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 61005714949544353578516485 11438571553039566295971841)
            ·
              refine ⟨8578928664779674721978881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11438571553039566295971841 8578928664779674721978881)
              ·
                refine ⟨6434196498584756041484161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8578928664779674721978881 6434196498584756041484161)
                ·
                  refine ⟨4825647373938567031113121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6434196498584756041484161 4825647373938567031113121)
                  ·
                    refine ⟨3619235530453925273334841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4825647373938567031113121 3619235530453925273334841)
                    ·
                      refine ⟨2714426647840443955001131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3619235530453925273334841 2714426647840443955001131)
                      ·
                        rfl

theorem cell23_5286327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 2, 2, 2, 2, 2].length) (baseStart_5286327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5286327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5286327 prefixEnd_5286327 := by exact prefixLift 5286327
  have htrace : WordTrace (prefixWord ++ tailWord_5286327) baseStart_5286327 baseEnd_5286327 := by
    simpa [prefixWord, tailWord_5286327, baseEnd_5286327] using wordTrace_append hprefix tailTrace_5286327
  have hstable : (prefixWord ++ tailWord_5286327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5286327).length < 2 ^ (prefixWord ++ tailWord_5286327).sum := by decide
  have hdescent : baseEnd_5286327 < baseStart_5286327 := by decide
  rcases family_descends (prefixWord ++ tailWord_5286327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5286337 : List Nat := [1, 2, 7, 1, 1, 1, 1, 1, 2, 6]
def baseStart_5286337 : Nat := 118140960795 + 5286337 * 2 ^ 59
def prefixEnd_5286337 : Nat := 4983230072969 + 3 ^ 40 * 5286337 * 2
def baseEnd_5286337 : Nat := 904810594215662971958695

theorem tailTrace_5286337 : CollatzResearch.WordTrace tailWord_5286337 prefixEnd_5286337 904810594215662971958695 := by
  unfold tailWord_5286337
  simp only [CollatzResearch.WordTrace]
  refine ⟨192808550249511358326385265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128539033499674238884256843 192808550249511358326385265)
  ·
    refine ⟨144606412687133518744788949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192808550249511358326385265 144606412687133518744788949)
    ·
      refine ⟨3389212797354691845580991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 144606412687133518744788949 3389212797354691845580991)
      ·
        refine ⟨5083819196032037768371487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3389212797354691845580991 5083819196032037768371487)
        ·
          refine ⟨7625728794048056652557231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5083819196032037768371487 7625728794048056652557231)
          ·
            refine ⟨11438593191072084978835847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7625728794048056652557231 11438593191072084978835847)
            ·
              refine ⟨17157889786608127468253771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11438593191072084978835847 17157889786608127468253771)
              ·
                refine ⟨25736834679912191202380657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17157889786608127468253771 25736834679912191202380657)
                ·
                  refine ⟨19302626009934143401785493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25736834679912191202380657 19302626009934143401785493)
                  ·
                    refine ⟨904810594215662971958695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19302626009934143401785493 904810594215662971958695)
                    ·
                      rfl

theorem cell23_5286337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 1, 1, 2, 6].length) (baseStart_5286337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5286337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5286337 prefixEnd_5286337 := by exact prefixLift 5286337
  have htrace : WordTrace (prefixWord ++ tailWord_5286337) baseStart_5286337 baseEnd_5286337 := by
    simpa [prefixWord, tailWord_5286337, baseEnd_5286337] using wordTrace_append hprefix tailTrace_5286337
  have hstable : (prefixWord ++ tailWord_5286337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5286337).length < 2 ^ (prefixWord ++ tailWord_5286337).sum := by decide
  have hdescent : baseEnd_5286337 < baseStart_5286337 := by decide
  rcases family_descends (prefixWord ++ tailWord_5286337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5286340 : List Nat := [2, 3, 3, 2, 2, 1, 1, 1, 2, 2, 4]
def baseStart_5286340 : Nat := 118140960795 + 5286340 * 2 ^ 59
def prefixEnd_5286340 : Nat := 4983230072969 + 3 ^ 40 * 5286340 * 2
def baseEnd_5286340 : Nat := 2714433323088952404138571

theorem tailTrace_5286340 : CollatzResearch.WordTrace tailWord_5286340 prefixEnd_5286340 2714433323088952404138571 := by
  unfold tailWord_5286340
  simp only [CollatzResearch.WordTrace]
  refine ⟨96404329834250244919372237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128539106445666993225829649 96404329834250244919372237)
  ·
    refine ⟨36151623687843841844764589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96404329834250244919372237 36151623687843841844764589)
    ·
      refine ⟨13556858882941440691786721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36151623687843841844764589 13556858882941440691786721)
      ·
        refine ⟨10167644162206080518840041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13556858882941440691786721 10167644162206080518840041)
        ·
          refine ⟨7625733121654560389130031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10167644162206080518840041 7625733121654560389130031)
          ·
            refine ⟨11438599682481840583695047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7625733121654560389130031 11438599682481840583695047)
            ·
              refine ⟨17157899523722760875542571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11438599682481840583695047 17157899523722760875542571)
              ·
                refine ⟨25736849285584141313313857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17157899523722760875542571 25736849285584141313313857)
                ·
                  refine ⟨19302636964188105984985393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25736849285584141313313857 19302636964188105984985393)
                  ·
                    refine ⟨14476977723141079488739045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19302636964188105984985393 14476977723141079488739045)
                    ·
                      refine ⟨2714433323088952404138571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14476977723141079488739045 2714433323088952404138571)
                      ·
                        rfl

theorem cell23_5286340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 1, 1, 2, 2, 4].length) (baseStart_5286340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5286340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5286340 prefixEnd_5286340 := by exact prefixLift 5286340
  have htrace : WordTrace (prefixWord ++ tailWord_5286340) baseStart_5286340 baseEnd_5286340 := by
    simpa [prefixWord, tailWord_5286340, baseEnd_5286340] using wordTrace_append hprefix tailTrace_5286340
  have hstable : (prefixWord ++ tailWord_5286340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5286340).length < 2 ^ (prefixWord ++ tailWord_5286340).sum := by decide
  have hdescent : baseEnd_5286340 < baseStart_5286340 := by decide
  rcases family_descends (prefixWord ++ tailWord_5286340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5286343 : List Nat := [1, 1, 4, 1, 1, 5, 1, 1, 2, 3, 3]
def baseStart_5286343 : Nat := 118140960795 + 5286343 * 2 ^ 59
def prefixEnd_5286343 : Nat := 4983230072969 + 3 ^ 40 * 5286343 * 2
def baseEnd_5286343 : Nat := 2714434863530915892401057

theorem tailTrace_5286343 : CollatzResearch.WordTrace tailWord_5286343 prefixEnd_5286343 2714434863530915892401057 := by
  unfold tailWord_5286343
  simp only [CollatzResearch.WordTrace]
  refine ⟨192808769087489621351103683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128539179391659747567402455 192808769087489621351103683)
  ·
    refine ⟨289213153631234432026655525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192808769087489621351103683 289213153631234432026655525)
    ·
      refine ⟨54227466305856456004997911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 289213153631234432026655525 54227466305856456004997911)
      ·
        refine ⟨81341199458784684007496867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54227466305856456004997911 81341199458784684007496867)
        ·
          refine ⟨122011799188177026011245301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81341199458784684007496867 122011799188177026011245301)
          ·
            refine ⟨11438606173891596188554247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 122011799188177026011245301 11438606173891596188554247)
            ·
              refine ⟨17157909260837394282831371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11438606173891596188554247 17157909260837394282831371)
              ·
                refine ⟨25736863891256091424247057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17157909260837394282831371 25736863891256091424247057)
                ·
                  refine ⟨19302647918442068568185293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25736863891256091424247057 19302647918442068568185293)
                  ·
                    refine ⟨7238492969415775713069485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19302647918442068568185293 7238492969415775713069485)
                    ·
                      refine ⟨2714434863530915892401057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7238492969415775713069485 2714434863530915892401057)
                      ·
                        rfl

theorem cell23_5286343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 1, 1, 2, 3, 3].length) (baseStart_5286343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5286343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5286343 prefixEnd_5286343 := by exact prefixLift 5286343
  have htrace : WordTrace (prefixWord ++ tailWord_5286343) baseStart_5286343 baseEnd_5286343 := by
    simpa [prefixWord, tailWord_5286343, baseEnd_5286343] using wordTrace_append hprefix tailTrace_5286343
  have hstable : (prefixWord ++ tailWord_5286343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5286343).length < 2 ^ (prefixWord ++ tailWord_5286343).sum := by decide
  have hdescent : baseEnd_5286343 < baseStart_5286343 := by decide
  rcases family_descends (prefixWord ++ tailWord_5286343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5286346 : List Nat := [3, 1, 2, 1, 2, 2, 2, 2, 1, 7]
def baseStart_5286346 : Nat := 118140960795 + 5286346 * 2 ^ 59
def prefixEnd_5286346 : Nat := 4983230072969 + 3 ^ 40 * 5286346 * 2
def baseEnd_5286346 : Nat := 904812134657626460221181

theorem tailTrace_5286346 : CollatzResearch.WordTrace tailWord_5286346 prefixEnd_5286346 904812134657626460221181 := by
  unfold tailWord_5286346
  simp only [CollatzResearch.WordTrace]
  refine ⟨48202219626619688215865723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128539252337652501908975261 48202219626619688215865723)
  ·
    refine ⟨72303329439929532323798585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48202219626619688215865723 72303329439929532323798585)
    ·
      refine ⟨54227497079947149242848939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72303329439929532323798585 54227497079947149242848939)
      ·
        refine ⟨81341245619920723864273409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54227497079947149242848939 81341245619920723864273409)
        ·
          refine ⟨61005934214940542898205057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81341245619920723864273409 61005934214940542898205057)
          ·
            refine ⟨45754450661205407173653793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61005934214940542898205057 45754450661205407173653793)
            ·
              refine ⟨34315837995904055380240345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45754450661205407173653793 34315837995904055380240345)
              ·
                refine ⟨25736878496928041535180259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34315837995904055380240345 25736878496928041535180259)
                ·
                  refine ⟨38605317745392062302770389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25736878496928041535180259 38605317745392062302770389)
                  ·
                    refine ⟨904812134657626460221181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38605317745392062302770389 904812134657626460221181)
                    ·
                      rfl

theorem cell23_5286346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 2, 1, 7].length) (baseStart_5286346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5286346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5286346 prefixEnd_5286346 := by exact prefixLift 5286346
  have htrace : WordTrace (prefixWord ++ tailWord_5286346) baseStart_5286346 baseEnd_5286346 := by
    simpa [prefixWord, tailWord_5286346, baseEnd_5286346] using wordTrace_append hprefix tailTrace_5286346
  have hstable : (prefixWord ++ tailWord_5286346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5286346).length < 2 ^ (prefixWord ++ tailWord_5286346).sum := by decide
  have hdescent : baseEnd_5286346 < baseStart_5286346 := by decide
  rcases family_descends (prefixWord ++ tailWord_5286346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5286393 : List Nat := [1, 2, 1, 3, 1, 2, 3, 3, 3, 4]
def baseStart_5286393 : Nat := 118140960795 + 5286393 * 2 ^ 59
def prefixEnd_5286393 : Nat := 4983230072969 + 3 ^ 40 * 5286393 * 2
def baseEnd_5286393 : Nat := 904820179187880232258609

theorem tailTrace_5286393 : CollatzResearch.WordTrace tailWord_5286393 prefixEnd_5286393 904820179187880232258609 := by
  unfold tailWord_5286393
  simp only [CollatzResearch.WordTrace]
  refine ⟨192810592737308479890423833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128540395158205653260282555 192810592737308479890423833)
  ·
    refine ⟨144607944552981359917817875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192810592737308479890423833 144607944552981359917817875)
    ·
      refine ⟨216911916829472039876726813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144607944552981359917817875 216911916829472039876726813)
      ·
        refine ⟨81341968811052014953772555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 216911916829472039876726813 81341968811052014953772555)
        ·
          refine ⟨122012953216578022430658833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81341968811052014953772555 122012953216578022430658833)
          ·
            refine ⟨91509714912433516822994125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 122012953216578022430658833 91509714912433516822994125)
            ·
              refine ⟨34316143092162568808622797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 91509714912433516822994125 34316143092162568808622797)
              ·
                refine ⟨12868553659560963303233549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34316143092162568808622797 12868553659560963303233549)
                ·
                  refine ⟨4825707622335361238712581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12868553659560963303233549 4825707622335361238712581)
                  ·
                    refine ⟨904820179187880232258609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4825707622335361238712581 904820179187880232258609)
                    ·
                      rfl

theorem cell23_5286393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 3, 3, 4].length) (baseStart_5286393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5286393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5286393 prefixEnd_5286393 := by exact prefixLift 5286393
  have htrace : WordTrace (prefixWord ++ tailWord_5286393) baseStart_5286393 baseEnd_5286393 := by
    simpa [prefixWord, tailWord_5286393, baseEnd_5286393] using wordTrace_append hprefix tailTrace_5286393
  have hstable : (prefixWord ++ tailWord_5286393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5286393).length < 2 ^ (prefixWord ++ tailWord_5286393).sum := by decide
  have hdescent : baseEnd_5286393 < baseStart_5286393 := by decide
  rcases family_descends (prefixWord ++ tailWord_5286393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5286396 : List Nat := [2, 2, 2, 1, 2, 1, 1, 1, 4, 1, 6]
def baseStart_5286396 : Nat := 118140960795 + 5286396 * 2 ^ 59
def prefixEnd_5286396 : Nat := 4983230072969 + 3 ^ 40 * 5286396 * 2
def baseEnd_5286396 : Nat := 2714462078005604185038313

theorem tailTrace_5286396 : CollatzResearch.WordTrace tailWord_5286396 prefixEnd_5286396 2714462078005604185038313 := by
  unfold tailWord_5286396
  simp only [CollatzResearch.WordTrace]
  refine ⟨96405351078148805701391521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128540468104198407601855361 96405351078148805701391521)
  ·
    refine ⟨72304013308611604276043641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96405351078148805701391521 72304013308611604276043641)
    ·
      refine ⟨54228009981458703207032731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72304013308611604276043641 54228009981458703207032731)
      ·
        refine ⟨81342014972188054810549097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54228009981458703207032731 81342014972188054810549097)
        ·
          refine ⟨61006511229141041107911823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81342014972188054810549097 61006511229141041107911823)
          ·
            refine ⟨91509766843711561661867735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61006511229141041107911823 91509766843711561661867735)
            ·
              refine ⟨137264650265567342492801603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91509766843711561661867735 137264650265567342492801603)
              ·
                refine ⟨205896975398351013739202405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 137264650265567342492801603 205896975398351013739202405)
                ·
                  refine ⟨38605682887190815076100451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 205896975398351013739202405 38605682887190815076100451)
                  ·
                    refine ⟨57908524330786222614150677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 38605682887190815076100451 57908524330786222614150677)
                    ·
                      refine ⟨2714462078005604185038313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 57908524330786222614150677 2714462078005604185038313)
                      ·
                        rfl

theorem cell23_5286396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 1, 4, 1, 6].length) (baseStart_5286396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5286396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5286396 prefixEnd_5286396 := by exact prefixLift 5286396
  have htrace : WordTrace (prefixWord ++ tailWord_5286396) baseStart_5286396 baseEnd_5286396 := by
    simpa [prefixWord, tailWord_5286396, baseEnd_5286396] using wordTrace_append hprefix tailTrace_5286396
  have hstable : (prefixWord ++ tailWord_5286396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5286396).length < 2 ^ (prefixWord ++ tailWord_5286396).sum := by decide
  have hdescent : baseEnd_5286396 < baseStart_5286396 := by decide
  rcases family_descends (prefixWord ++ tailWord_5286396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5286453 : List Nat := [1, 3, 3, 1, 1, 2, 2, 2, 3, 5]
def baseStart_5286453 : Nat := 118140960795 + 5286453 * 2 ^ 59
def prefixEnd_5286453 : Nat := 4983230072969 + 3 ^ 40 * 5286453 * 2
def baseEnd_5286453 : Nat := 904830448800970154008517

theorem tailTrace_5286453 : CollatzResearch.WordTrace tailWord_5286453 prefixEnd_5286453 904830448800970154008517 := by
  unfold tailWord_5286453
  simp only [CollatzResearch.WordTrace]
  refine ⟨192812781117091110137608013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128541854078060740091738675 192812781117091110137608013)
  ·
    refine ⟨72304792918909166301603005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 192812781117091110137608013 72304792918909166301603005)
    ·
      refine ⟨27114297344590937363101127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72304792918909166301603005 27114297344590937363101127)
      ·
        refine ⟨40671446016886406044651691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27114297344590937363101127 40671446016886406044651691)
        ·
          refine ⟨61007169025329609066977537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40671446016886406044651691 61007169025329609066977537)
          ·
            refine ⟨45755376768997206800233153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61007169025329609066977537 45755376768997206800233153)
            ·
              refine ⟨34316532576747905100174865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45755376768997206800233153 34316532576747905100174865)
              ·
                refine ⟨25737399432560928825131149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34316532576747905100174865 25737399432560928825131149)
                ·
                  refine ⟨9651524787210348309424181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25737399432560928825131149 9651524787210348309424181)
                  ·
                    refine ⟨904830448800970154008517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9651524787210348309424181 904830448800970154008517)
                    ·
                      rfl

theorem cell23_5286453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 2, 3, 5].length) (baseStart_5286453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5286453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5286453 prefixEnd_5286453 := by exact prefixLift 5286453
  have htrace : WordTrace (prefixWord ++ tailWord_5286453) baseStart_5286453 baseEnd_5286453 := by
    simpa [prefixWord, tailWord_5286453, baseEnd_5286453] using wordTrace_append hprefix tailTrace_5286453
  have hstable : (prefixWord ++ tailWord_5286453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5286453).length < 2 ^ (prefixWord ++ tailWord_5286453).sum := by decide
  have hdescent : baseEnd_5286453 < baseStart_5286453 := by decide
  rcases family_descends (prefixWord ++ tailWord_5286453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5286503 : List Nat := [1, 1, 5, 1, 1, 1, 1, 1, 5, 2, 4]
def baseStart_5286503 : Nat := 118140960795 + 5286503 * 2 ^ 59
def prefixEnd_5286503 : Nat := 4983230072969 + 3 ^ 40 * 5286503 * 2
def baseEnd_5286503 : Nat := 2714517020435635266400321

theorem tailTrace_5286503 : CollatzResearch.WordTrace tailWord_5286503 prefixEnd_5286503 2714517020435635266400321 := by
  unfold tailWord_5286503
  simp only [CollatzResearch.WordTrace]
  refine ⟨192814604766909968676928163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128543069844606645784618775 192814604766909968676928163)
  ·
    refine ⟨289221907150364953015392245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192814604766909968676928163 289221907150364953015392245)
    ·
      refine ⟨27114553795346714345193023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 289221907150364953015392245 27114553795346714345193023)
      ·
        refine ⟨40671830693020071517789535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27114553795346714345193023 40671830693020071517789535)
        ·
          refine ⟨61007746039530107276684303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40671830693020071517789535 61007746039530107276684303)
          ·
            refine ⟨91511619059295160915026455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61007746039530107276684303 91511619059295160915026455)
            ·
              refine ⟨137267428588942741372539683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91511619059295160915026455 137267428588942741372539683)
              ·
                refine ⟨205901142883414112058809525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 137267428588942741372539683 205901142883414112058809525)
                ·
                  refine ⟨19303232145320073005513393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 205901142883414112058809525 19303232145320073005513393)
                  ·
                    refine ⟨14477424108990054754135045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19303232145320073005513393 14477424108990054754135045)
                    ·
                      refine ⟨2714517020435635266400321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14477424108990054754135045 2714517020435635266400321)
                      ·
                        rfl

theorem cell23_5286503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 1, 5, 2, 4].length) (baseStart_5286503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5286503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5286503 prefixEnd_5286503 := by exact prefixLift 5286503
  have htrace : WordTrace (prefixWord ++ tailWord_5286503) baseStart_5286503 baseEnd_5286503 := by
    simpa [prefixWord, tailWord_5286503, baseEnd_5286503] using wordTrace_append hprefix tailTrace_5286503
  have hstable : (prefixWord ++ tailWord_5286503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5286503).length < 2 ^ (prefixWord ++ tailWord_5286503).sum := by decide
  have hdescent : baseEnd_5286503 < baseStart_5286503 := by decide
  rcases family_descends (prefixWord ++ tailWord_5286503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5286517 : List Nat := [1, 3, 4, 2, 2, 1, 2, 1, 1, 6]
def baseStart_5286517 : Nat := 118140960795 + 5286517 * 2 ^ 59
def prefixEnd_5286517 : Nat := 4983230072969 + 3 ^ 40 * 5286517 * 2
def baseEnd_5286517 : Nat := 904841403054932737208419

theorem tailTrace_5286517 : CollatzResearch.WordTrace tailWord_5286517 prefixEnd_5286517 904841403054932737208419 := by
  unfold tailWord_5286517
  simp only [CollatzResearch.WordTrace]
  refine ⟨192815115388859249067937805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128543410259239499378625203 192815115388859249067937805)
  ·
    refine ⟨72305668270822218400476677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 192815115388859249067937805 72305668270822218400476677)
    ·
      refine ⟨13557312800779165950089377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 72305668270822218400476677 13557312800779165950089377)
      ·
        refine ⟨10167984600584374462567033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13557312800779165950089377 10167984600584374462567033)
        ·
          refine ⟨7625988450438280846925275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10167984600584374462567033 7625988450438280846925275)
          ·
            refine ⟨11438982675657421270387913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7625988450438280846925275 11438982675657421270387913)
            ·
              refine ⟨8579237006743065952790935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11438982675657421270387913 8579237006743065952790935)
              ·
                refine ⟨12868855510114598929186403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8579237006743065952790935 12868855510114598929186403)
                ·
                  refine ⟨19303283265171898393779605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12868855510114598929186403 19303283265171898393779605)
                  ·
                    refine ⟨904841403054932737208419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19303283265171898393779605 904841403054932737208419)
                    ·
                      rfl

theorem cell23_5286517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 2, 1, 1, 6].length) (baseStart_5286517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5286517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5286517 prefixEnd_5286517 := by exact prefixLift 5286517
  have htrace : WordTrace (prefixWord ++ tailWord_5286517) baseStart_5286517 baseEnd_5286517 := by
    simpa [prefixWord, tailWord_5286517, baseEnd_5286517] using wordTrace_append hprefix tailTrace_5286517
  have hstable : (prefixWord ++ tailWord_5286517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5286517).length < 2 ^ (prefixWord ++ tailWord_5286517).sum := by decide
  have hdescent : baseEnd_5286517 < baseStart_5286517 := by decide
  rcases family_descends (prefixWord ++ tailWord_5286517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5286563 : List Nat := [1, 1, 1, 4, 1, 1, 2, 3, 2, 3, 4]
def baseStart_5286563 : Nat := 118140960795 + 5286563 * 2 ^ 59
def prefixEnd_5286563 : Nat := 4983230072969 + 3 ^ 40 * 5286563 * 2
def baseEnd_5286563 : Nat := 2714547829274905031650045

theorem tailTrace_5286563 : CollatzResearch.WordTrace tailWord_5286563 prefixEnd_5286563 2714547829274905031650045 := by
  unfold tailWord_5286563
  simp only [CollatzResearch.WordTrace]
  refine ⟨192816793146692598924112343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128544528764461732616074895 192816793146692598924112343)
  ·
    refine ⟨289225189720038898386168515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192816793146692598924112343 289225189720038898386168515)
    ·
      refine ⟨433837784580058347579252773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 289225189720038898386168515 433837784580058347579252773)
      ·
        refine ⟨81344584608760940171109895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 433837784580058347579252773 81344584608760940171109895)
        ·
          refine ⟨122016876913141410256664843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81344584608760940171109895 122016876913141410256664843)
          ·
            refine ⟨183025315369712115384997265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122016876913141410256664843 183025315369712115384997265)
            ·
              refine ⟨137268986527284086538747949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 183025315369712115384997265 137268986527284086538747949)
              ·
                refine ⟨51475869947731532452030481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 137268986527284086538747949 51475869947731532452030481)
                ·
                  refine ⟨38606902460798649339022861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51475869947731532452030481 38606902460798649339022861)
                  ·
                    refine ⟨14477588422799493502133573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 38606902460798649339022861 14477588422799493502133573)
                    ·
                      refine ⟨2714547829274905031650045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14477588422799493502133573 2714547829274905031650045)
                      ·
                        rfl

theorem cell23_5286563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 3, 2, 3, 4].length) (baseStart_5286563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5286563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5286563 prefixEnd_5286563 := by exact prefixLift 5286563
  have htrace : WordTrace (prefixWord ++ tailWord_5286563) baseStart_5286563 baseEnd_5286563 := by
    simpa [prefixWord, tailWord_5286563, baseEnd_5286563] using wordTrace_append hprefix tailTrace_5286563
  have hstable : (prefixWord ++ tailWord_5286563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5286563).length < 2 ^ (prefixWord ++ tailWord_5286563).sum := by decide
  have hdescent : baseEnd_5286563 < baseStart_5286563 := by decide
  rcases family_descends (prefixWord ++ tailWord_5286563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5286574 : List Nat := [4, 1, 4, 1, 1, 1, 3, 1, 1, 3, 3]
def baseStart_5286574 : Nat := 118140960795 + 5286574 * 2 ^ 59
def prefixEnd_5286574 : Nat := 4983230072969 + 3 ^ 40 * 5286574 * 2
def baseEnd_5286574 : Nat := 2714553477562104488612495

theorem tailTrace_5286574 : CollatzResearch.WordTrace tailWord_5286574 prefixEnd_5286574 2714553477562104488612495 := by
  unfold tailWord_5286574
  simp only [CollatzResearch.WordTrace]
  refine ⟨24102149293706593475345347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 128544796233101831868508517 24102149293706593475345347)
  ·
    refine ⟨36153223940559890213018021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24102149293706593475345347 36153223940559890213018021)
    ·
      refine ⟨6778729488854979414940879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36153223940559890213018021 6778729488854979414940879)
      ·
        refine ⟨10168094233282469122411319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6778729488854979414940879 10168094233282469122411319)
        ·
          refine ⟨15252141349923703683616979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10168094233282469122411319 15252141349923703683616979)
          ·
            refine ⟨22878212024885555525425469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15252141349923703683616979 22878212024885555525425469)
            ·
              refine ⟨8579329509332083322034551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22878212024885555525425469 8579329509332083322034551)
              ·
                refine ⟨12868994263998124983051827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8579329509332083322034551 12868994263998124983051827)
                ·
                  refine ⟨19303491395997187474577741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12868994263998124983051827 19303491395997187474577741)
                  ·
                    refine ⟨7238809273498945302966653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19303491395997187474577741 7238809273498945302966653)
                    ·
                      refine ⟨2714553477562104488612495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7238809273498945302966653 2714553477562104488612495)
                      ·
                        rfl

theorem cell23_5286574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 3, 1, 1, 3, 3].length) (baseStart_5286574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5286574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5286574 prefixEnd_5286574 := by exact prefixLift 5286574
  have htrace : WordTrace (prefixWord ++ tailWord_5286574) baseStart_5286574 baseEnd_5286574 := by
    simpa [prefixWord, tailWord_5286574, baseEnd_5286574] using wordTrace_append hprefix tailTrace_5286574
  have hstable : (prefixWord ++ tailWord_5286574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5286574).length < 2 ^ (prefixWord ++ tailWord_5286574).sum := by decide
  have hdescent : baseEnd_5286574 < baseStart_5286574 := by decide
  rcases family_descends (prefixWord ++ tailWord_5286574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5286600 : List Nat := [2, 1, 3, 1, 2, 4, 1, 1, 2, 1, 5]
def baseStart_5286600 : Nat := 118140960795 + 5286600 * 2 ^ 59
def prefixEnd_5286600 : Nat := 4983230072969 + 3 ^ 40 * 5286600 * 2
def baseEnd_5286600 : Nat := 2714566828059121386887375

theorem tailTrace_5286600 : CollatzResearch.WordTrace tailWord_5286600 prefixEnd_5286600 2714566828059121386887375 := by
  unfold tailWord_5286600
  simp only [CollatzResearch.WordTrace]
  refine ⟨96409071323779277121604627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128545428431705702828806169 96409071323779277121604627)
  ·
    refine ⟨144613606985668915682406941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96409071323779277121604627 144613606985668915682406941)
    ·
      refine ⟨54230102619625843380902603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 144613606985668915682406941 54230102619625843380902603)
      ·
        refine ⟨81345153929438765071353905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54230102619625843380902603 81345153929438765071353905)
        ·
          refine ⟨61008865447079073803515429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81345153929438765071353905 61008865447079073803515429)
          ·
            refine ⟨11439162271327326338159143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 61008865447079073803515429 11439162271327326338159143)
            ·
              refine ⟨17158743406990989507238715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11439162271327326338159143 17158743406990989507238715)
              ·
                refine ⟨25738115110486484260858073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17158743406990989507238715 25738115110486484260858073)
                ·
                  refine ⟨19303586332864863195643555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25738115110486484260858073 19303586332864863195643555)
                  ·
                    refine ⟨28955379499297294793465333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19303586332864863195643555 28955379499297294793465333)
                    ·
                      refine ⟨2714566828059121386887375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28955379499297294793465333 2714566828059121386887375)
                      ·
                        rfl

theorem cell23_5286600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 1, 1, 2, 1, 5].length) (baseStart_5286600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5286600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5286600 prefixEnd_5286600 := by exact prefixLift 5286600
  have htrace : WordTrace (prefixWord ++ tailWord_5286600) baseStart_5286600 baseEnd_5286600 := by
    simpa [prefixWord, tailWord_5286600, baseEnd_5286600] using wordTrace_append hprefix tailTrace_5286600
  have hstable : (prefixWord ++ tailWord_5286600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5286600).length < 2 ^ (prefixWord ++ tailWord_5286600).sum := by decide
  have hdescent : baseEnd_5286600 < baseStart_5286600 := by decide
  rcases family_descends (prefixWord ++ tailWord_5286600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5286633 : List Nat := [1, 2, 1, 1, 1, 2, 4, 1, 3, 7]
def baseStart_5286633 : Nat := 118140960795 + 5286633 * 2 ^ 59
def prefixEnd_5286633 : Nat := 4983230072969 + 3 ^ 40 * 5286633 * 2
def baseEnd_5286633 : Nat := 904861257640239919258241

theorem tailTrace_5286633 : CollatzResearch.WordTrace tailWord_5286633 prefixEnd_5286633 904861257640239919258241 := by
  unfold tailWord_5286633
  simp only [CollatzResearch.WordTrace]
  refine ⟨192819346256439000879160553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128546230837626000586107035 192819346256439000879160553)
  ·
    refine ⟨144614509692329250659370415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192819346256439000879160553 144614509692329250659370415)
    ·
      refine ⟨216921764538493875989055623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144614509692329250659370415 216921764538493875989055623)
      ·
        refine ⟨325382646807740813983583435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 216921764538493875989055623 325382646807740813983583435)
        ·
          refine ⟨488073970211611220975375153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 325382646807740813983583435 488073970211611220975375153)
          ·
            refine ⟨366055477658708415731531365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 488073970211611220975375153 366055477658708415731531365)
            ·
              refine ⟨68635402061007827949662131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 366055477658708415731531365 68635402061007827949662131)
              ·
                refine ⟨102953103091511741924493197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68635402061007827949662131 102953103091511741924493197)
                ·
                  refine ⟨38607413659316903221684949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 102953103091511741924493197 38607413659316903221684949)
                  ·
                    refine ⟨904861257640239919258241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38607413659316903221684949 904861257640239919258241)
                    ·
                      rfl

theorem cell23_5286633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 1, 3, 7].length) (baseStart_5286633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5286633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5286633 prefixEnd_5286633 := by exact prefixLift 5286633
  have htrace : WordTrace (prefixWord ++ tailWord_5286633) baseStart_5286633 baseEnd_5286633 := by
    simpa [prefixWord, tailWord_5286633, baseEnd_5286633] using wordTrace_append hprefix tailTrace_5286633
  have hstable : (prefixWord ++ tailWord_5286633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5286633).length < 2 ^ (prefixWord ++ tailWord_5286633).sum := by decide
  have hdescent : baseEnd_5286633 < baseStart_5286633 := by decide
  rcases family_descends (prefixWord ++ tailWord_5286633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5286643 : List Nat := [1, 1, 1, 2, 2, 3, 1, 1, 3, 1, 7]
def baseStart_5286643 : Nat := 118140960795 + 5286643 * 2 ^ 59
def prefixEnd_5286643 : Nat := 4983230072969 + 3 ^ 40 * 5286643 * 2
def baseEnd_5286643 : Nat := 2714588907727264718649677

theorem tailTrace_5286643 : CollatzResearch.WordTrace tailWord_5286643 prefixEnd_5286643 2714588907727264718649677 := by
  unfold tailWord_5286643
  simp only [CollatzResearch.WordTrace]
  refine ⟨192819710986402772587024583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128546473990935181724683055 192819710986402772587024583)
  ·
    refine ⟨289229566479604158880536875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192819710986402772587024583 289229566479604158880536875)
    ·
      refine ⟨433844349719406238320805313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 289229566479604158880536875 433844349719406238320805313)
      ·
        refine ⟨325383262289554678740603985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 433844349719406238320805313 325383262289554678740603985)
        ·
          refine ⟨244037446717166009055452989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 325383262289554678740603985 244037446717166009055452989)
          ·
            refine ⟨91514042518937253395794871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 244037446717166009055452989 91514042518937253395794871)
            ·
              refine ⟨137271063778405880093692307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91514042518937253395794871 137271063778405880093692307)
              ·
                refine ⟨205906595667608820140538461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 137271063778405880093692307 205906595667608820140538461)
                ·
                  refine ⟨77214973375353307552701923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 205906595667608820140538461 77214973375353307552701923)
                  ·
                    refine ⟨115822460063029961329052885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 77214973375353307552701923 115822460063029961329052885)
                    ·
                      refine ⟨2714588907727264718649677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 115822460063029961329052885 2714588907727264718649677)
                      ·
                        rfl

theorem cell23_5286643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 1, 3, 1, 7].length) (baseStart_5286643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5286643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5286643 prefixEnd_5286643 := by exact prefixLift 5286643
  have htrace : WordTrace (prefixWord ++ tailWord_5286643) baseStart_5286643 baseEnd_5286643 := by
    simpa [prefixWord, tailWord_5286643, baseEnd_5286643] using wordTrace_append hprefix tailTrace_5286643
  have hstable : (prefixWord ++ tailWord_5286643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5286643).length < 2 ^ (prefixWord ++ tailWord_5286643).sum := by decide
  have hdescent : baseEnd_5286643 < baseStart_5286643 := by decide
  rcases family_descends (prefixWord ++ tailWord_5286643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5286650 : List Nat := [3, 1, 1, 1, 1, 3, 3, 3, 2, 5]
def baseStart_5286650 : Nat := 118140960795 + 5286650 * 2 ^ 59
def prefixEnd_5286650 : Nat := 4983230072969 + 3 ^ 40 * 5286650 * 2
def baseEnd_5286650 : Nat := 904864167363948730420715

theorem tailTrace_5286650 : CollatzResearch.WordTrace tailWord_5286650 prefixEnd_5286650 904864167363948730420715 := by
  unfold tailWord_5286650
  simp only [CollatzResearch.WordTrace]
  refine ⟨48204991574344353195632351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128546644198251608521686269 48204991574344353195632351)
  ·
    refine ⟨72307487361516529793448527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48204991574344353195632351 72307487361516529793448527)
    ·
      refine ⟨108461231042274794690172791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72307487361516529793448527 108461231042274794690172791)
      ·
        refine ⟨162691846563412192035259187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108461231042274794690172791 162691846563412192035259187)
        ·
          refine ⟨244037769845118288052888781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162691846563412192035259187 244037769845118288052888781)
          ·
            refine ⟨91514163691919358019833293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 244037769845118288052888781 91514163691919358019833293)
            ·
              refine ⟨34317811384469759257437485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 91514163691919358019833293 34317811384469759257437485)
              ·
                refine ⟨12869179269176159721539057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34317811384469759257437485 12869179269176159721539057)
                ·
                  refine ⟨9651884451882119791154293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12869179269176159721539057 9651884451882119791154293)
                  ·
                    refine ⟨904864167363948730420715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9651884451882119791154293 904864167363948730420715)
                    ·
                      rfl

theorem cell23_5286650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 3, 2, 5].length) (baseStart_5286650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5286650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5286650 prefixEnd_5286650 := by exact prefixLift 5286650
  have htrace : WordTrace (prefixWord ++ tailWord_5286650) baseStart_5286650 baseEnd_5286650 := by
    simpa [prefixWord, tailWord_5286650, baseEnd_5286650] using wordTrace_append hprefix tailTrace_5286650
  have hstable : (prefixWord ++ tailWord_5286650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5286650).length < 2 ^ (prefixWord ++ tailWord_5286650).sum := by decide
  have hdescent : baseEnd_5286650 < baseStart_5286650 := by decide
  rcases family_descends (prefixWord ++ tailWord_5286650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5286660 : List Nat := [2, 3, 2, 2, 1, 1, 1, 1, 3, 2, 5]
def baseStart_5286660 : Nat := 118140960795 + 5286660 * 2 ^ 59
def prefixEnd_5286660 : Nat := 4983230072969 + 3 ^ 40 * 5286660 * 2
def baseEnd_5286660 : Nat := 2714597636898391152137099

theorem tailTrace_5286660 : CollatzResearch.WordTrace tailWord_5286660 prefixEnd_5286660 2714597636898391152137099 := by
  unfold tailWord_5286660
  simp only [CollatzResearch.WordTrace]
  refine ⟨96410165513670592245196717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128546887351560789660262289 96410165513670592245196717)
  ·
    refine ⟨36153812067626472091948769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96410165513670592245196717 36153812067626472091948769)
    ·
      refine ⟨27115359050719854068961577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36153812067626472091948769 27115359050719854068961577)
      ·
        refine ⟨20336519288039890551721183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27115359050719854068961577 20336519288039890551721183)
        ·
          refine ⟨30504778932059835827581775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20336519288039890551721183 30504778932059835827581775)
          ·
            refine ⟨45757168398089753741372663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30504778932059835827581775 45757168398089753741372663)
            ·
              refine ⟨68635752597134630612058995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45757168398089753741372663 68635752597134630612058995)
              ·
                refine ⟨102953628895701945918088493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68635752597134630612058995 102953628895701945918088493)
                ·
                  refine ⟨38607610835888229719283185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 102953628895701945918088493 38607610835888229719283185)
                  ·
                    refine ⟨28955708126916172289462389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 38607610835888229719283185 28955708126916172289462389)
                    ·
                      refine ⟨2714597636898391152137099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28955708126916172289462389 2714597636898391152137099)
                      ·
                        rfl

theorem cell23_5286660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 1, 3, 2, 5].length) (baseStart_5286660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5286660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5286660 prefixEnd_5286660 := by exact prefixLift 5286660
  have htrace : WordTrace (prefixWord ++ tailWord_5286660) baseStart_5286660 baseEnd_5286660 := by
    simpa [prefixWord, tailWord_5286660, baseEnd_5286660] using wordTrace_append hprefix tailTrace_5286660
  have hstable : (prefixWord ++ tailWord_5286660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5286660).length < 2 ^ (prefixWord ++ tailWord_5286660).sum := by decide
  have hdescent : baseEnd_5286660 < baseStart_5286660 := by decide
  rcases family_descends (prefixWord ++ tailWord_5286660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5286670 : List Nat := [4, 1, 1, 2, 1, 1, 1, 2, 3, 3, 4]
def baseStart_5286670 : Nat := 118140960795 + 5286670 * 2 ^ 59
def prefixEnd_5286670 : Nat := 4983230072969 + 3 ^ 40 * 5286670 * 2
def baseEnd_5286670 : Nat := 2714602771704936113012053

theorem tailTrace_5286670 : CollatzResearch.WordTrace tailWord_5286670 prefixEnd_5286670 2714602771704936113012053 := by
  unfold tailWord_5286670
  simp only [CollatzResearch.WordTrace]
  refine ⟨24102586969663119524782183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 128547130504869970798838309 24102586969663119524782183)
  ·
    refine ⟨36153880454494679287173275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24102586969663119524782183 36153880454494679287173275)
    ·
      refine ⟨54230820681742018930759913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36153880454494679287173275 54230820681742018930759913)
      ·
        refine ⟨40673115511306514198069935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54230820681742018930759913 40673115511306514198069935)
        ·
          refine ⟨61009673266959771297104903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40673115511306514198069935 61009673266959771297104903)
          ·
            refine ⟨91514509900439656945657355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61009673266959771297104903 91514509900439656945657355)
            ·
              refine ⟨137271764850659485418486033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91514509900439656945657355 137271764850659485418486033)
              ·
                refine ⟨102953823637994614063864525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 137271764850659485418486033 102953823637994614063864525)
                ·
                  refine ⟨38607683864247980273949197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 102953823637994614063864525 38607683864247980273949197)
                  ·
                    refine ⟨14477881449092992602730949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 38607683864247980273949197 14477881449092992602730949)
                    ·
                      refine ⟨2714602771704936113012053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14477881449092992602730949 2714602771704936113012053)
                      ·
                        rfl

theorem cell23_5286670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 2, 3, 3, 4].length) (baseStart_5286670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5286670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5286670 prefixEnd_5286670 := by exact prefixLift 5286670
  have htrace : WordTrace (prefixWord ++ tailWord_5286670) baseStart_5286670 baseEnd_5286670 := by
    simpa [prefixWord, tailWord_5286670, baseEnd_5286670] using wordTrace_append hprefix tailTrace_5286670
  have hstable : (prefixWord ++ tailWord_5286670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5286670).length < 2 ^ (prefixWord ++ tailWord_5286670).sum := by decide
  have hdescent : baseEnd_5286670 < baseStart_5286670 := by decide
  rcases family_descends (prefixWord ++ tailWord_5286670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5286687 : List Nat := [1, 1, 2, 4, 2, 2, 1, 1, 1, 6, 2]
def baseStart_5286687 : Nat := 118140960795 + 5286687 * 2 ^ 59
def prefixEnd_5286687 : Nat := 4983230072969 + 3 ^ 40 * 5286687 * 2
def baseEnd_5286687 : Nat := 2714611500876062546499475

theorem tailTrace_5286687 : CollatzResearch.WordTrace tailWord_5286687 prefixEnd_5286687 2714611500876062546499475 := by
  unfold tailWord_5286687
  simp only [CollatzResearch.WordTrace]
  refine ⟨192821315798243368101626315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128547543865495578734417543 192821315798243368101626315)
  ·
    refine ⟨289231973697365052152439473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192821315798243368101626315 289231973697365052152439473)
    ·
      refine ⟨216923980273023789114329605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 289231973697365052152439473 216923980273023789114329605)
      ·
        refine ⟨40673246301191960458936801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 216923980273023789114329605 40673246301191960458936801)
        ·
          refine ⟨30504934725893970344202601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40673246301191960458936801 30504934725893970344202601)
          ·
            refine ⟨22878701044420477758151951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30504934725893970344202601 22878701044420477758151951)
            ·
              refine ⟨34318051566630716637227927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22878701044420477758151951 34318051566630716637227927)
              ·
                refine ⟨51477077349946074955841891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34318051566630716637227927 51477077349946074955841891)
                ·
                  refine ⟨77215616024919112433762837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51477077349946074955841891 77215616024919112433762837)
                  ·
                    refine ⟨3619482001168083395332633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 77215616024919112433762837 3619482001168083395332633)
                    ·
                      refine ⟨2714611500876062546499475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3619482001168083395332633 2714611500876062546499475)
                      ·
                        rfl

theorem cell23_5286687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 1, 1, 6, 2].length) (baseStart_5286687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5286687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5286687 prefixEnd_5286687 := by exact prefixLift 5286687
  have htrace : WordTrace (prefixWord ++ tailWord_5286687) baseStart_5286687 baseEnd_5286687 := by
    simpa [prefixWord, tailWord_5286687, baseEnd_5286687] using wordTrace_append hprefix tailTrace_5286687
  have hstable : (prefixWord ++ tailWord_5286687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5286687).length < 2 ^ (prefixWord ++ tailWord_5286687).sum := by decide
  have hdescent : baseEnd_5286687 < baseStart_5286687 := by decide
  rcases family_descends (prefixWord ++ tailWord_5286687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5286707 : List Nat := [1, 1, 1, 2, 6, 2, 1, 1, 1, 4, 3]
def baseStart_5286707 : Nat := 118140960795 + 5286707 * 2 ^ 59
def prefixEnd_5286707 : Nat := 4983230072969 + 3 ^ 40 * 5286707 * 2
def baseEnd_5286707 : Nat := 2714621770489152468249383

theorem tailTrace_5286707 : CollatzResearch.WordTrace tailWord_5286707 prefixEnd_5286707 2714621770489152468249383 := by
  unfold tailWord_5286707
  simp only [CollatzResearch.WordTrace]
  refine ⟨192822045258170911517354375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128548030172113941011569583 192822045258170911517354375)
  ·
    refine ⟨289233067887256367276031563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192822045258170911517354375 289233067887256367276031563)
    ·
      refine ⟨433849601830884550914047345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 289233067887256367276031563 433849601830884550914047345)
      ·
        refine ⟨325387201373163413185535509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 433849601830884550914047345 325387201373163413185535509)
        ·
          refine ⟨15252525064367034993071977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 325387201373163413185535509 15252525064367034993071977)
          ·
            refine ⟨11439393798275276244803983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15252525064367034993071977 11439393798275276244803983)
            ·
              refine ⟨17159090697412914367205975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11439393798275276244803983 17159090697412914367205975)
              ·
                refine ⟨25738636046119371550808963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17159090697412914367205975 25738636046119371550808963)
                ·
                  refine ⟨38607954069179057326213445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25738636046119371550808963 38607954069179057326213445)
                  ·
                    refine ⟨7238991387971073248665021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 38607954069179057326213445 7238991387971073248665021)
                    ·
                      refine ⟨2714621770489152468249383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7238991387971073248665021 2714621770489152468249383)
                      ·
                        rfl

theorem cell23_5286707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 1, 1, 1, 4, 3].length) (baseStart_5286707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5286707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5286707 prefixEnd_5286707 := by exact prefixLift 5286707
  have htrace : WordTrace (prefixWord ++ tailWord_5286707) baseStart_5286707 baseEnd_5286707 := by
    simpa [prefixWord, tailWord_5286707, baseEnd_5286707] using wordTrace_append hprefix tailTrace_5286707
  have hstable : (prefixWord ++ tailWord_5286707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5286707).length < 2 ^ (prefixWord ++ tailWord_5286707).sum := by decide
  have hdescent : baseEnd_5286707 < baseStart_5286707 := by decide
  rcases family_descends (prefixWord ++ tailWord_5286707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5286720 : List Nat := [2, 1, 1, 2, 2, 1, 1, 2, 1, 7, 3]
def baseStart_5286720 : Nat := 118140960795 + 5286720 * 2 ^ 59
def prefixEnd_5286720 : Nat := 4983230072969 + 3 ^ 40 * 5286720 * 2
def baseEnd_5286720 : Nat := 2714628445737660917386823

theorem tailTrace_5286720 : CollatzResearch.WordTrace tailWord_5286720 prefixEnd_5286720 2714628445737660917386823 := by
  unfold tailWord_5286720
  simp only [CollatzResearch.WordTrace]
  refine ⟨96411259703561907368788807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128548346271415876491718409 96411259703561907368788807)
  ·
    refine ⟨144616889555342861053183211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96411259703561907368788807 144616889555342861053183211)
    ·
      refine ⟨216925334333014291579774817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144616889555342861053183211 216925334333014291579774817)
      ·
        refine ⟨162694000749760718684831113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 216925334333014291579774817 162694000749760718684831113)
        ·
          refine ⟨122020500562320539013623335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 162694000749760718684831113 122020500562320539013623335)
          ·
            refine ⟨183030750843480808520435003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122020500562320539013623335 183030750843480808520435003)
            ·
              refine ⟨274546126265221212780652505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 183030750843480808520435003 274546126265221212780652505)
              ·
                refine ⟨205909594698915909585489379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 274546126265221212780652505 205909594698915909585489379)
                ·
                  refine ⟨308864392048373864378234069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 205909594698915909585489379 308864392048373864378234069)
                  ·
                    refine ⟨7239009188633762446364861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 308864392048373864378234069 7239009188633762446364861)
                    ·
                      refine ⟨2714628445737660917386823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7239009188633762446364861 2714628445737660917386823)
                      ·
                        rfl

theorem cell23_5286720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 1, 7, 3].length) (baseStart_5286720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5286720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5286720 prefixEnd_5286720 := by exact prefixLift 5286720
  have htrace : WordTrace (prefixWord ++ tailWord_5286720) baseStart_5286720 baseEnd_5286720 := by
    simpa [prefixWord, tailWord_5286720, baseEnd_5286720] using wordTrace_append hprefix tailTrace_5286720
  have hstable : (prefixWord ++ tailWord_5286720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5286720).length < 2 ^ (prefixWord ++ tailWord_5286720).sum := by decide
  have hdescent : baseEnd_5286720 < baseStart_5286720 := by decide
  rcases family_descends (prefixWord ++ tailWord_5286720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5286757 : List Nat := [1, 3, 1, 3, 1, 1, 3, 4, 1, 5]
def baseStart_5286757 : Nat := 118140960795 + 5286757 * 2 ^ 59
def prefixEnd_5286757 : Nat := 4983230072969 + 3 ^ 40 * 5286757 * 2
def baseEnd_5286757 : Nat := 904882481507292424208051

theorem tailTrace_5286757 : CollatzResearch.WordTrace tailWord_5286757 prefixEnd_5286757 904882481507292424208051 := by
  unfold tailWord_5286757
  simp only [CollatzResearch.WordTrace]
  refine ⟨192823868907989770056674525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128549245938659846704449683 192823868907989770056674525)
  ·
    refine ⟨72308950840496163771252947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 192823868907989770056674525 72308950840496163771252947)
    ·
      refine ⟨108463426260744245656879421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72308950840496163771252947 108463426260744245656879421)
      ·
        refine ⟨40673784847779092121329783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 108463426260744245656879421 40673784847779092121329783)
        ·
          refine ⟨61010677271668638181994675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40673784847779092121329783 61010677271668638181994675)
          ·
            refine ⟨91516015907502957272992013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61010677271668638181994675 91516015907502957272992013)
            ·
              refine ⟨34318505965313608977372005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 91516015907502957272992013 34318505965313608977372005)
              ·
                refine ⟨6434719868496301683257251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34318505965313608977372005 6434719868496301683257251)
                ·
                  refine ⟨9652079802744452524885877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6434719868496301683257251 9652079802744452524885877)
                  ·
                    refine ⟨904882481507292424208051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9652079802744452524885877 904882481507292424208051)
                    ·
                      rfl

theorem cell23_5286757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 4, 1, 5].length) (baseStart_5286757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5286757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5286757 prefixEnd_5286757 := by exact prefixLift 5286757
  have htrace : WordTrace (prefixWord ++ tailWord_5286757) baseStart_5286757 baseEnd_5286757 := by
    simpa [prefixWord, tailWord_5286757, baseEnd_5286757] using wordTrace_append hprefix tailTrace_5286757
  have hstable : (prefixWord ++ tailWord_5286757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5286757).length < 2 ^ (prefixWord ++ tailWord_5286757).sum := by decide
  have hdescent : baseEnd_5286757 < baseStart_5286757 := by decide
  rcases family_descends (prefixWord ++ tailWord_5286757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5286764 : List Nat := [2, 2, 1, 1, 4, 1, 2, 3, 2, 3, 2]
def baseStart_5286764 : Nat := 118140960795 + 5286764 * 2 ^ 59
def prefixEnd_5286764 : Nat := 4983230072969 + 3 ^ 40 * 5286764 * 2
def baseEnd_5286764 : Nat := 2714651038886458745236621

theorem tailTrace_5286764 : CollatzResearch.WordTrace tailWord_5286764 prefixEnd_5286764 2714651038886458745236621 := by
  unfold tailWord_5286764
  simp only [CollatzResearch.WordTrace]
  refine ⟨96412062109482205126089673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128549416145976273501452897 96412062109482205126089673)
  ·
    refine ⟨72309046582111653844567255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96412062109482205126089673 72309046582111653844567255)
    ·
      refine ⟨108463569873167480766850883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72309046582111653844567255 108463569873167480766850883)
      ·
        refine ⟨162695354809751221150276325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108463569873167480766850883 162695354809751221150276325)
        ·
          refine ⟨30505379026828353965676811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 162695354809751221150276325 30505379026828353965676811)
          ·
            refine ⟨45758068540242530948515217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30505379026828353965676811 45758068540242530948515217)
            ·
              refine ⟨34318551405181898211386413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45758068540242530948515217 34318551405181898211386413)
              ·
                refine ⟨12869456776943211829269905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34318551405181898211386413 12869456776943211829269905)
                ·
                  refine ⟨9652092582707408871952429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12869456776943211829269905 9652092582707408871952429)
                  ·
                    refine ⟨3619534718515278326982161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9652092582707408871952429 3619534718515278326982161)
                    ·
                      refine ⟨2714651038886458745236621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3619534718515278326982161 2714651038886458745236621)
                      ·
                        rfl

theorem cell23_5286764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 3, 2].length) (baseStart_5286764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5286764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5286764 prefixEnd_5286764 := by exact prefixLift 5286764
  have htrace : WordTrace (prefixWord ++ tailWord_5286764) baseStart_5286764 baseEnd_5286764 := by
    simpa [prefixWord, tailWord_5286764, baseEnd_5286764] using wordTrace_append hprefix tailTrace_5286764
  have hstable : (prefixWord ++ tailWord_5286764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5286764).length < 2 ^ (prefixWord ++ tailWord_5286764).sum := by decide
  have hdescent : baseEnd_5286764 < baseStart_5286764 := by decide
  rcases family_descends (prefixWord ++ tailWord_5286764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5286771 : List Nat := [1, 1, 1, 2, 2, 1, 7, 3, 1, 1, 3]
def baseStart_5286771 : Nat := 118140960795 + 5286771 * 2 ^ 59
def prefixEnd_5286771 : Nat := 4983230072969 + 3 ^ 40 * 5286771 * 2
def baseEnd_5286771 : Nat := 2714654633251040217849089

theorem tailTrace_5286771 : CollatzResearch.WordTrace tailWord_5286771 prefixEnd_5286771 2714654633251040217849089 := by
  unfold tailWord_5286771
  simp only [CollatzResearch.WordTrace]
  refine ⟨192824379529939050447684167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128549586353292700298456111 192824379529939050447684167)
  ·
    refine ⟨289236569294908575671526251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192824379529939050447684167 289236569294908575671526251)
    ·
      refine ⟨433854853942362863507289377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 289236569294908575671526251 433854853942362863507289377)
      ·
        refine ⟨325391140456772147630467033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 433854853942362863507289377 325391140456772147630467033)
        ·
          refine ⟨244043355342579110722850275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 325391140456772147630467033 244043355342579110722850275)
          ·
            refine ⟨366065033013868666084275413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 244043355342579110722850275 366065033013868666084275413)
            ·
              refine ⟨8579649211262546861350205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 366065033013868666084275413 8579649211262546861350205)
              ·
                refine ⟨3217368454223455073006327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8579649211262546861350205 3217368454223455073006327)
                ·
                  refine ⟨4826052681335182609509491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3217368454223455073006327 4826052681335182609509491)
                  ·
                    refine ⟨7239079022002773914264237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4826052681335182609509491 7239079022002773914264237)
                    ·
                      refine ⟨2714654633251040217849089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7239079022002773914264237 2714654633251040217849089)
                      ·
                        rfl

theorem cell23_5286771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 7, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 7, 3, 1, 1, 3].length) (baseStart_5286771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5286771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5286771 prefixEnd_5286771 := by exact prefixLift 5286771
  have htrace : WordTrace (prefixWord ++ tailWord_5286771) baseStart_5286771 baseEnd_5286771 := by
    simpa [prefixWord, tailWord_5286771, baseEnd_5286771] using wordTrace_append hprefix tailTrace_5286771
  have hstable : (prefixWord ++ tailWord_5286771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5286771).length < 2 ^ (prefixWord ++ tailWord_5286771).sum := by decide
  have hdescent : baseEnd_5286771 < baseStart_5286771 := by decide
  rcases family_descends (prefixWord ++ tailWord_5286771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5286787 : List Nat := [1, 1, 1, 3, 4, 1, 1, 3, 4, 4]
def baseStart_5286787 : Nat := 118140960795 + 5286787 * 2 ^ 59
def prefixEnd_5286787 : Nat := 4983230072969 + 3 ^ 40 * 5286787 * 2
def baseEnd_5286787 : Nat := 904887616313837385083005

theorem tailTrace_5286787 : CollatzResearch.WordTrace tailWord_5286787 prefixEnd_5286787 904887616313837385083005 := by
  unfold tailWord_5286787
  simp only [CollatzResearch.WordTrace]
  refine ⟨192824963097881085180266615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128549975398587390120177743 192824963097881085180266615)
  ·
    refine ⟨289237444646821627770399923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192824963097881085180266615 289237444646821627770399923)
    ·
      refine ⟨433856166970232441655599885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 289237444646821627770399923 433856166970232441655599885)
      ·
        refine ⟨162696062613837165620849957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 433856166970232441655599885 162696062613837165620849957)
        ·
          refine ⟨30505511740094468553909367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 162696062613837165620849957 30505511740094468553909367)
          ·
            refine ⟨45758267610141702830864051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30505511740094468553909367 45758267610141702830864051)
            ·
              refine ⟨68637401415212554246296077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45758267610141702830864051 68637401415212554246296077)
              ·
                refine ⟨25739025530704707842361029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 68637401415212554246296077 25739025530704707842361029)
                ·
                  refine ⟨4826067287007132720442693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25739025530704707842361029 4826067287007132720442693)
                  ·
                    refine ⟨904887616313837385083005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4826067287007132720442693 904887616313837385083005)
                    ·
                      rfl

theorem cell23_5286787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 3, 4, 4].length) (baseStart_5286787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5286787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5286787 prefixEnd_5286787 := by exact prefixLift 5286787
  have htrace : WordTrace (prefixWord ++ tailWord_5286787) baseStart_5286787 baseEnd_5286787 := by
    simpa [prefixWord, tailWord_5286787, baseEnd_5286787] using wordTrace_append hprefix tailTrace_5286787
  have hstable : (prefixWord ++ tailWord_5286787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5286787).length < 2 ^ (prefixWord ++ tailWord_5286787).sum := by decide
  have hdescent : baseEnd_5286787 < baseStart_5286787 := by decide
  rcases family_descends (prefixWord ++ tailWord_5286787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5286807 : List Nat := [1, 1, 3, 3, 1, 2, 2, 3, 1, 2, 4]
def baseStart_5286807 : Nat := 118140960795 + 5286807 * 2 ^ 59
def prefixEnd_5286807 : Nat := 4983230072969 + 3 ^ 40 * 5286807 * 2
def baseEnd_5286807 : Nat := 2714673118554602076998923

theorem tailTrace_5286807 : CollatzResearch.WordTrace tailWord_5286807 prefixEnd_5286807 2714673118554602076998923 := by
  unfold tailWord_5286807
  simp only [CollatzResearch.WordTrace]
  refine ⟨192825692557808628595994675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128550461705205752397329783 192825692557808628595994675)
  ·
    refine ⟨289238538836712942893992013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192825692557808628595994675 289238538836712942893992013)
    ·
      refine ⟨108464452063767353585247005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 289238538836712942893992013 108464452063767353585247005)
      ·
        refine ⟨40674169523912757594467627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 108464452063767353585247005 40674169523912757594467627)
        ·
          refine ⟨61011254285869136391701441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40674169523912757594467627 61011254285869136391701441)
          ·
            refine ⟨45758440714401852293776081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61011254285869136391701441 45758440714401852293776081)
            ·
              refine ⟨34318830535801389220332061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45758440714401852293776081 34318830535801389220332061)
              ·
                refine ⟨12869561450925520957624523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34318830535801389220332061 12869561450925520957624523)
                ·
                  refine ⟨19304342176388281436436785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12869561450925520957624523 19304342176388281436436785)
                  ·
                    refine ⟨14478256632291211077327589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19304342176388281436436785 14478256632291211077327589)
                    ·
                      refine ⟨2714673118554602076998923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14478256632291211077327589 2714673118554602076998923)
                      ·
                        rfl

theorem cell23_5286807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 3, 1, 2, 4].length) (baseStart_5286807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5286807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5286807 prefixEnd_5286807 := by exact prefixLift 5286807
  have htrace : WordTrace (prefixWord ++ tailWord_5286807) baseStart_5286807 baseEnd_5286807 := by
    simpa [prefixWord, tailWord_5286807, baseEnd_5286807] using wordTrace_append hprefix tailTrace_5286807
  have hstable : (prefixWord ++ tailWord_5286807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5286807).length < 2 ^ (prefixWord ++ tailWord_5286807).sum := by decide
  have hdescent : baseEnd_5286807 < baseStart_5286807 := by decide
  rcases family_descends (prefixWord ++ tailWord_5286807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5286817 : List Nat := [1, 2, 3, 4, 1, 1, 2, 9]
def baseStart_5286817 : Nat := 118140960795 + 5286817 * 2 ^ 59
def prefixEnd_5286817 : Nat := 4983230072969 + 3 ^ 40 * 5286817 * 2
def baseEnd_5286817 : Nat := 100543639013375816217551

theorem tailTrace_5286817 : CollatzResearch.WordTrace tailWord_5286817 prefixEnd_5286817 100543639013375816217551 := by
  unfold tailWord_5286817
  simp only [CollatzResearch.WordTrace]
  refine ⟨192826057287772400303858705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128550704858514933535905803 192826057287772400303858705)
  ·
    refine ⟨144619542965829300227894029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192826057287772400303858705 144619542965829300227894029)
    ·
      refine ⟨54232328612185987585460261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 144619542965829300227894029 54232328612185987585460261)
      ·
        refine ⟨10168561614784872672273799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54232328612185987585460261 10168561614784872672273799)
        ·
          refine ⟨15252842422177309008410699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10168561614784872672273799 15252842422177309008410699)
          ·
            refine ⟨22879263633265963512616049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15252842422177309008410699 22879263633265963512616049)
            ·
              refine ⟨17159447724949472634462037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22879263633265963512616049 17159447724949472634462037)
              ·
                refine ⟨100543639013375816217551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 17159447724949472634462037 100543639013375816217551)
                ·
                  rfl

theorem cell23_5286817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 2, 9].length) (baseStart_5286817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5286817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5286817 prefixEnd_5286817 := by exact prefixLift 5286817
  have htrace : WordTrace (prefixWord ++ tailWord_5286817) baseStart_5286817 baseEnd_5286817 := by
    simpa [prefixWord, tailWord_5286817, baseEnd_5286817] using wordTrace_append hprefix tailTrace_5286817
  have hstable : (prefixWord ++ tailWord_5286817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5286817).length < 2 ^ (prefixWord ++ tailWord_5286817).sum := by decide
  have hdescent : baseEnd_5286817 < baseStart_5286817 := by decide
  rcases family_descends (prefixWord ++ tailWord_5286817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5286827 : List Nat := [1, 1, 1, 1, 2, 1, 1, 8, 1, 3, 3]
def baseStart_5286827 : Nat := 118140960795 + 5286827 * 2 ^ 59
def prefixEnd_5286827 : Nat := 4983230072969 + 3 ^ 40 * 5286827 * 2
def baseEnd_5286827 : Nat := 2714683388167691998748831

theorem tailTrace_5286827 : CollatzResearch.WordTrace tailWord_5286827 prefixEnd_5286827 2714683388167691998748831 := by
  unfold tailWord_5286827
  simp only [CollatzResearch.WordTrace]
  refine ⟨192826422017736172011722735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128550948011824114674481823 192826422017736172011722735)
  ·
    refine ⟨289239633026604258017584103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192826422017736172011722735 289239633026604258017584103)
    ·
      refine ⟨433859449539906387026376155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 289239633026604258017584103 433859449539906387026376155)
      ·
        refine ⟨650789174309859580539564233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 433859449539906387026376155 650789174309859580539564233)
        ·
          refine ⟨488091880732394685404673175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 650789174309859580539564233 488091880732394685404673175)
          ·
            refine ⟨732137821098592028107009763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 488091880732394685404673175 732137821098592028107009763)
            ·
              refine ⟨1098206731647888042160514645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 732137821098592028107009763 1098206731647888042160514645)
              ·
                refine ⟨12869610136498687994068531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1098206731647888042160514645 12869610136498687994068531)
                ·
                  refine ⟨19304415204748031991102797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12869610136498687994068531 19304415204748031991102797)
                  ·
                    refine ⟨7239155701780511996663549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19304415204748031991102797 7239155701780511996663549)
                    ·
                      refine ⟨2714683388167691998748831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7239155701780511996663549 2714683388167691998748831)
                      ·
                        rfl

theorem cell23_5286827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 8, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 8, 1, 3, 3].length) (baseStart_5286827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5286827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5286827 prefixEnd_5286827 := by exact prefixLift 5286827
  have htrace : WordTrace (prefixWord ++ tailWord_5286827) baseStart_5286827 baseEnd_5286827 := by
    simpa [prefixWord, tailWord_5286827, baseEnd_5286827] using wordTrace_append hprefix tailTrace_5286827
  have hstable : (prefixWord ++ tailWord_5286827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5286827).length < 2 ^ (prefixWord ++ tailWord_5286827).sum := by decide
  have hdescent : baseEnd_5286827 < baseStart_5286827 := by decide
  rcases family_descends (prefixWord ++ tailWord_5286827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5286845 : List Nat := [1, 4, 1, 2, 4, 1, 1, 4, 1, 2, 2]
def baseStart_5286845 : Nat := 118140960795 + 5286845 * 2 ^ 59
def prefixEnd_5286845 : Nat := 4983230072969 + 3 ^ 40 * 5286845 * 2
def baseEnd_5286845 : Nat := 2714692630819472928323749

theorem tailTrace_5286845 : CollatzResearch.WordTrace tailWord_5286845 prefixEnd_5286845 2714692630819472928323749 := by
  unfold tailWord_5286845
  simp only [CollatzResearch.WordTrace]
  refine ⟨192827078531670961085877989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128551385687780640723918659 192827078531670961085877989)
  ·
    refine ⟨36155077224688305203602123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 192827078531670961085877989 36155077224688305203602123)
    ·
      refine ⟨54232615837032457805403185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36155077224688305203602123 54232615837032457805403185)
      ·
        refine ⟨40674461877774343354052389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54232615837032457805403185 40674461877774343354052389)
        ·
          refine ⟨7626461602082689378884823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40674461877774343354052389 7626461602082689378884823)
          ·
            refine ⟨11439692403124034068327235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7626461602082689378884823 11439692403124034068327235)
            ·
              refine ⟨17159538604686051102490853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11439692403124034068327235 17159538604686051102490853)
              ·
                refine ⟨3217413488378634581717035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17159538604686051102490853 3217413488378634581717035)
                ·
                  refine ⟨4826120232567951872575553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3217413488378634581717035 4826120232567951872575553)
                  ·
                    refine ⟨3619590174425963904431665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4826120232567951872575553 3619590174425963904431665)
                    ·
                      refine ⟨2714692630819472928323749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3619590174425963904431665 2714692630819472928323749)
                      ·
                        rfl

theorem cell23_5286845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 1, 4, 1, 2, 2].length) (baseStart_5286845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5286845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5286845 prefixEnd_5286845 := by exact prefixLift 5286845
  have htrace : WordTrace (prefixWord ++ tailWord_5286845) baseStart_5286845 baseEnd_5286845 := by
    simpa [prefixWord, tailWord_5286845, baseEnd_5286845] using wordTrace_append hprefix tailTrace_5286845
  have hstable : (prefixWord ++ tailWord_5286845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5286845).length < 2 ^ (prefixWord ++ tailWord_5286845).sum := by decide
  have hdescent : baseEnd_5286845 < baseStart_5286845 := by decide
  rcases family_descends (prefixWord ++ tailWord_5286845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5286884 : List Nat := [2, 3, 1, 1, 1, 1, 2, 3, 3, 4, 2]
def baseStart_5286884 : Nat := 118140960795 + 5286884 * 2 ^ 59
def prefixEnd_5286884 : Nat := 4983230072969 + 3 ^ 40 * 5286884 * 2
def baseEnd_5286884 : Nat := 2714712656564998275736069

theorem tailTrace_5286884 : CollatzResearch.WordTrace tailWord_5286884 prefixEnd_5286884 2714712656564998275736069 := by
  unfold tailWord_5286884
  simp only [CollatzResearch.WordTrace]
  refine ⟨96414250489264835373273853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128552333985686447164365137 96414250489264835373273853)
  ·
    refine ⟨36155343933474313264977695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96414250489264835373273853 36155343933474313264977695)
    ·
      refine ⟨54233015900211469897466543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36155343933474313264977695 54233015900211469897466543)
      ·
        refine ⟨81349523850317204846199815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54233015900211469897466543 81349523850317204846199815)
        ·
          refine ⟨122024285775475807269299723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81349523850317204846199815 122024285775475807269299723)
          ·
            refine ⟨183036428663213710903949585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122024285775475807269299723 183036428663213710903949585)
            ·
              refine ⟨137277321497410283177962189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 183036428663213710903949585 137277321497410283177962189)
              ·
                refine ⟨51478995561528856191735821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 137277321497410283177962189 51478995561528856191735821)
                ·
                  refine ⟨19304623335573321071900933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51478995561528856191735821 19304623335573321071900933)
                  ·
                    refine ⟨3619616875419997700981425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19304623335573321071900933 3619616875419997700981425)
                    ·
                      refine ⟨2714712656564998275736069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3619616875419997700981425 2714712656564998275736069)
                      ·
                        rfl

theorem cell23_5286884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 3, 3, 4, 2].length) (baseStart_5286884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5286884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5286884 prefixEnd_5286884 := by exact prefixLift 5286884
  have htrace : WordTrace (prefixWord ++ tailWord_5286884) baseStart_5286884 baseEnd_5286884 := by
    simpa [prefixWord, tailWord_5286884, baseEnd_5286884] using wordTrace_append hprefix tailTrace_5286884
  have hstable : (prefixWord ++ tailWord_5286884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5286884).length < 2 ^ (prefixWord ++ tailWord_5286884).sum := by decide
  have hdescent : baseEnd_5286884 < baseStart_5286884 := by decide
  rcases family_descends (prefixWord ++ tailWord_5286884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5286888 : List Nat := [2, 1, 4, 1, 1, 1, 6, 1, 1, 3, 2]
def baseStart_5286888 : Nat := 118140960795 + 5286888 * 2 ^ 59
def prefixEnd_5286888 : Nat := 4983230072969 + 3 ^ 40 * 5286888 * 2
def baseEnd_5286888 : Nat := 2714714710487616260086051

theorem tailTrace_5286888 : CollatzResearch.WordTrace tailWord_5286888 prefixEnd_5286888 2714714710487616260086051 := by
  unfold tailWord_5286888
  simp only [CollatzResearch.WordTrace]
  refine ⟨96414323435257589714846659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128552431247010119619795545 96414323435257589714846659)
  ·
    refine ⟨144621485152886384572269989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96414323435257589714846659 144621485152886384572269989)
    ·
      refine ⟨27116528466166197107300623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 144621485152886384572269989 27116528466166197107300623)
      ·
        refine ⟨40674792699249295660950935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27116528466166197107300623 40674792699249295660950935)
        ·
          refine ⟨61012189048873943491426403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40674792699249295660950935 61012189048873943491426403)
          ·
            refine ⟨91518283573310915237139605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61012189048873943491426403 91518283573310915237139605)
            ·
              refine ⟨4289919542498949151740919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 91518283573310915237139605 4289919542498949151740919)
              ·
                refine ⟨6434879313748423727611379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4289919542498949151740919 6434879313748423727611379)
                ·
                  refine ⟨9652318970622635591417069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6434879313748423727611379 9652318970622635591417069)
                  ·
                    refine ⟨3619619613983488346781401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9652318970622635591417069 3619619613983488346781401)
                    ·
                      refine ⟨2714714710487616260086051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3619619613983488346781401 2714714710487616260086051)
                      ·
                        rfl

theorem cell23_5286888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 6, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 6, 1, 1, 3, 2].length) (baseStart_5286888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5286888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5286888 prefixEnd_5286888 := by exact prefixLift 5286888
  have htrace : WordTrace (prefixWord ++ tailWord_5286888) baseStart_5286888 baseEnd_5286888 := by
    simpa [prefixWord, tailWord_5286888, baseEnd_5286888] using wordTrace_append hprefix tailTrace_5286888
  have hstable : (prefixWord ++ tailWord_5286888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5286888).length < 2 ^ (prefixWord ++ tailWord_5286888).sum := by decide
  have hdescent : baseEnd_5286888 < baseStart_5286888 := by decide
  rcases family_descends (prefixWord ++ tailWord_5286888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5286937 : List Nat := [1, 2, 1, 2, 1, 1, 6, 1, 1, 7]
def baseStart_5286937 : Nat := 118140960795 + 5286937 * 2 ^ 59
def prefixEnd_5286937 : Nat := 4983230072969 + 3 ^ 40 * 5286937 * 2
def baseEnd_5286937 : Nat := 904913290346562189457775

theorem tailTrace_5286937 : CollatzResearch.WordTrace tailWord_5286937 prefixEnd_5286937 904913290346562189457775 := by
  unfold tailWord_5286937
  simp only [CollatzResearch.WordTrace]
  refine ⟨192830434047337660798227065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128553622698225107198818043 192830434047337660798227065)
  ·
    refine ⟨144622825535503245598670299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192830434047337660798227065 144622825535503245598670299)
    ·
      refine ⟨216934238303254868398005449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144622825535503245598670299 216934238303254868398005449)
      ·
        refine ⟨162700678727441151298504087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 216934238303254868398005449 162700678727441151298504087)
        ·
          refine ⟨244051018091161726947756131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162700678727441151298504087 244051018091161726947756131)
          ·
            refine ⟨366076527136742590421634197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 244051018091161726947756131 366076527136742590421634197)
            ·
              refine ⟨17159837209534808926014103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 366076527136742590421634197 17159837209534808926014103)
              ·
                refine ⟨25739755814302213389021155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17159837209534808926014103 25739755814302213389021155)
                ·
                  refine ⟨38609633721453320083531733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25739755814302213389021155 38609633721453320083531733)
                  ·
                    refine ⟨904913290346562189457775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38609633721453320083531733 904913290346562189457775)
                    ·
                      rfl

theorem cell23_5286937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 6, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 6, 1, 1, 7].length) (baseStart_5286937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5286937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5286937 prefixEnd_5286937 := by exact prefixLift 5286937
  have htrace : WordTrace (prefixWord ++ tailWord_5286937) baseStart_5286937 baseEnd_5286937 := by
    simpa [prefixWord, tailWord_5286937, baseEnd_5286937] using wordTrace_append hprefix tailTrace_5286937
  have hstable : (prefixWord ++ tailWord_5286937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5286937).length < 2 ^ (prefixWord ++ tailWord_5286937).sum := by decide
  have hdescent : baseEnd_5286937 < baseStart_5286937 := by decide
  rcases family_descends (prefixWord ++ tailWord_5286937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5286958 : List Nat := [4, 1, 3, 1, 1, 1, 5, 2, 5]
def baseStart_5286958 : Nat := 118140960795 + 5286958 * 2 ^ 59
def prefixEnd_5286958 : Nat := 4983230072969 + 3 ^ 40 * 5286958 * 2
def baseEnd_5286958 : Nat := 301638961570381220690081

theorem tailTrace_5286958 : CollatzResearch.WordTrace tailWord_5286958 prefixEnd_5286958 301638961570381220690081 := by
  unfold tailWord_5286958
  simp only [CollatzResearch.WordTrace]
  refine ⟨24103899997532697673092691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 128554133320174387589827685 24103899997532697673092691)
  ·
    refine ⟨36155849996299046509639037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24103899997532697673092691 36155849996299046509639037)
    ·
      refine ⟨13558443748612142441114639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36155849996299046509639037 13558443748612142441114639)
      ·
        refine ⟨20337665622918213661671959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13558443748612142441114639 20337665622918213661671959)
        ·
          refine ⟨30506498434377320492507939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20337665622918213661671959 30506498434377320492507939)
          ·
            refine ⟨45759747651565980738761909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30506498434377320492507939 45759747651565980738761909)
            ·
              refine ⟨4289976342334310694258929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 45759747651565980738761909 4289976342334310694258929)
              ·
                refine ⟨3217482256750733020694197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4289976342334310694258929 3217482256750733020694197)
                ·
                  refine ⟨301638961570381220690081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3217482256750733020694197 301638961570381220690081)
                  ·
                    rfl

theorem cell23_5286958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 5, 2, 5].length) (baseStart_5286958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5286958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5286958 prefixEnd_5286958 := by exact prefixLift 5286958
  have htrace : WordTrace (prefixWord ++ tailWord_5286958) baseStart_5286958 baseEnd_5286958 := by
    simpa [prefixWord, tailWord_5286958, baseEnd_5286958] using wordTrace_append hprefix tailTrace_5286958
  have hstable : (prefixWord ++ tailWord_5286958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5286958).length < 2 ^ (prefixWord ++ tailWord_5286958).sum := by decide
  have hdescent : baseEnd_5286958 < baseStart_5286958 := by decide
  rcases family_descends (prefixWord ++ tailWord_5286958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5286984 : List Nat := [2, 1, 3, 1, 1, 1, 4, 1, 5, 4]
def baseStart_5286984 : Nat := 118140960795 + 5286984 * 2 ^ 59
def prefixEnd_5286984 : Nat := 4983230072969 + 3 ^ 40 * 5286984 * 2
def baseEnd_5286984 : Nat := 904921334876815961495203

theorem tailTrace_5286984 : CollatzResearch.WordTrace tailWord_5286984 prefixEnd_5286984 904921334876815961495203 := by
  unfold tailWord_5286984
  simp only [CollatzResearch.WordTrace]
  refine ⟨96416074139083693912594003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128554765518778258550125337 96416074139083693912594003)
  ·
    refine ⟨144624111208625540868891005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96416074139083693912594003 144624111208625540868891005)
    ·
      refine ⟨54234041703234577825834127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 144624111208625540868891005 54234041703234577825834127)
      ·
        refine ⟨81351062554851866738751191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54234041703234577825834127 81351062554851866738751191)
        ·
          refine ⟨122026593832277800108126787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81351062554851866738751191 122026593832277800108126787)
          ·
            refine ⟨183039890748416700162190181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122026593832277800108126787 183039890748416700162190181)
            ·
              refine ⟨34319979515328131280410659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 183039890748416700162190181 34319979515328131280410659)
              ·
                refine ⟨51479969272992196920615989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34319979515328131280410659 51479969272992196920615989)
                ·
                  refine ⟨4826247119343018461307749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 51479969272992196920615989 4826247119343018461307749)
                  ·
                    refine ⟨904921334876815961495203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4826247119343018461307749 904921334876815961495203)
                    ·
                      rfl

theorem cell23_5286984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 1, 5, 4].length) (baseStart_5286984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5286984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5286984 prefixEnd_5286984 := by exact prefixLift 5286984
  have htrace : WordTrace (prefixWord ++ tailWord_5286984) baseStart_5286984 baseEnd_5286984 := by
    simpa [prefixWord, tailWord_5286984, baseEnd_5286984] using wordTrace_append hprefix tailTrace_5286984
  have hstable : (prefixWord ++ tailWord_5286984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5286984).length < 2 ^ (prefixWord ++ tailWord_5286984).sum := by decide
  have hdescent : baseEnd_5286984 < baseStart_5286984 := by decide
  rcases family_descends (prefixWord ++ tailWord_5286984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5287004 : List Nat := [2, 2, 4, 1, 1, 1, 2, 1, 2, 1, 6]
def baseStart_5287004 : Nat := 118140960795 + 5287004 * 2 ^ 59
def prefixEnd_5287004 : Nat := 4983230072969 + 3 ^ 40 * 5287004 * 2
def baseEnd_5287004 : Nat := 2714774274243537806235517

theorem tailTrace_5287004 : CollatzResearch.WordTrace tailWord_5287004 prefixEnd_5287004 2714774274243537806235517 := by
  unfold tailWord_5287004
  simp only [CollatzResearch.WordTrace]
  refine ⟨96416438869047465620458033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128555251825396620827277377 96416438869047465620458033)
  ·
    refine ⟨72312329151785599215343525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96416438869047465620458033 72312329151785599215343525)
    ·
      refine ⟨13558561715959799852876911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 72312329151785599215343525 13558561715959799852876911)
      ·
        refine ⟨20337842573939699779315367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13558561715959799852876911 20337842573939699779315367)
        ·
          refine ⟨30506763860909549668973051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20337842573939699779315367 30506763860909549668973051)
          ·
            refine ⟨45760145791364324503459577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30506763860909549668973051 45760145791364324503459577)
            ·
              refine ⟨34320109343523243377594683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45760145791364324503459577 34320109343523243377594683)
              ·
                refine ⟨51480164015284865066392025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34320109343523243377594683 51480164015284865066392025)
                ·
                  refine ⟨38610123011463648799794019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51480164015284865066392025 38610123011463648799794019)
                  ·
                    refine ⟨57915184517195473199691029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 38610123011463648799794019 57915184517195473199691029)
                    ·
                      refine ⟨2714774274243537806235517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 57915184517195473199691029 2714774274243537806235517)
                      ·
                        rfl

theorem cell23_5287004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 1, 2, 1, 6].length) (baseStart_5287004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5287004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5287004 prefixEnd_5287004 := by exact prefixLift 5287004
  have htrace : WordTrace (prefixWord ++ tailWord_5287004) baseStart_5287004 baseEnd_5287004 := by
    simpa [prefixWord, tailWord_5287004, baseEnd_5287004] using wordTrace_append hprefix tailTrace_5287004
  have hstable : (prefixWord ++ tailWord_5287004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5287004).length < 2 ^ (prefixWord ++ tailWord_5287004).sum := by decide
  have hdescent : baseEnd_5287004 < baseStart_5287004 := by decide
  rcases family_descends (prefixWord ++ tailWord_5287004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5287045 : List Nat := [1, 3, 1, 1, 7, 1, 1, 1, 2, 2, 3]
def baseStart_5287045 : Nat := 118140960795 + 5287045 * 2 ^ 59
def prefixEnd_5287045 : Nat := 4983230072969 + 3 ^ 40 * 5287045 * 2
def baseEnd_5287045 : Nat := 2714795326950372145822829

theorem tailTrace_5287045 : CollatzResearch.WordTrace tailWord_5287045 prefixEnd_5287045 2714795326950372145822829 := by
  unfold tailWord_5287045
  simp only [CollatzResearch.WordTrace]
  refine ⟨192834373130946395243158589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128556248753964263495439059 192834373130946395243158589)
  ·
    refine ⟨72312889924104898216184471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 192834373130946395243158589 72312889924104898216184471)
    ·
      refine ⟨108469334886157347324276707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72312889924104898216184471 108469334886157347324276707)
      ·
        refine ⟨162704002329236020986415061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108469334886157347324276707 162704002329236020986415061)
        ·
          refine ⟨3813375054591469241869103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 162704002329236020986415061 3813375054591469241869103)
          ·
            refine ⟨5720062581887203862803655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3813375054591469241869103 5720062581887203862803655)
            ·
              refine ⟨8580093872830805794205483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5720062581887203862803655 8580093872830805794205483)
              ·
                refine ⟨12870140809246208691308225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8580093872830805794205483 12870140809246208691308225)
                ·
                  refine ⟨9652605606934656518481169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12870140809246208691308225 9652605606934656518481169)
                  ·
                    refine ⟨7239454205200992388860877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9652605606934656518481169 7239454205200992388860877)
                    ·
                      refine ⟨2714795326950372145822829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7239454205200992388860877 2714795326950372145822829)
                      ·
                        rfl

theorem cell23_5287045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 1, 1, 2, 2, 3].length) (baseStart_5287045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5287045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5287045 prefixEnd_5287045 := by exact prefixLift 5287045
  have htrace : WordTrace (prefixWord ++ tailWord_5287045) baseStart_5287045 baseEnd_5287045 := by
    simpa [prefixWord, tailWord_5287045, baseEnd_5287045] using wordTrace_append hprefix tailTrace_5287045
  have hstable : (prefixWord ++ tailWord_5287045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5287045).length < 2 ^ (prefixWord ++ tailWord_5287045).sum := by decide
  have hdescent : baseEnd_5287045 < baseStart_5287045 := by decide
  rcases family_descends (prefixWord ++ tailWord_5287045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5287084 : List Nat := [2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 3]
def baseStart_5287084 : Nat := 118140960795 + 5287084 * 2 ^ 59
def prefixEnd_5287084 : Nat := 4983230072969 + 3 ^ 40 * 5287084 * 2
def baseEnd_5287084 : Nat := 2714815352695897493235149

theorem tailTrace_5287084 : CollatzResearch.WordTrace tailWord_5287084 prefixEnd_5287084 2714815352695897493235149 := by
  unfold tailWord_5287084
  simp only [CollatzResearch.WordTrace]
  refine ⟨96417897788902552451914153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128557197051870069935885537 96417897788902552451914153)
  ·
    refine ⟨72313423341676914338935615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96417897788902552451914153 72313423341676914338935615)
    ·
      refine ⟨108470135012515371508403423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72313423341676914338935615 108470135012515371508403423)
      ·
        refine ⟨162705202518773057262605135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108470135012515371508403423 162705202518773057262605135)
        ·
          refine ⟨244057803778159585893907703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162705202518773057262605135 244057803778159585893907703)
          ·
            refine ⟨366086705667239378840861555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 244057803778159585893907703 366086705667239378840861555)
            ·
              refine ⟨549130058500859068261292333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 366086705667239378840861555 549130058500859068261292333)
              ·
                refine ⟨205923771937822150597984625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 549130058500859068261292333 205923771937822150597984625)
                ·
                  refine ⟨154442828953366612948488469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 205923771937822150597984625 154442828953366612948488469)
                  ·
                    refine ⟨7239507607189059981960397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 154442828953366612948488469 7239507607189059981960397)
                    ·
                      refine ⟨2714815352695897493235149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7239507607189059981960397 2714815352695897493235149)
                      ·
                        rfl

theorem cell23_5287084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 3].length) (baseStart_5287084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5287084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5287084 prefixEnd_5287084 := by exact prefixLift 5287084
  have htrace : WordTrace (prefixWord ++ tailWord_5287084) baseStart_5287084 baseEnd_5287084 := by
    simpa [prefixWord, tailWord_5287084, baseEnd_5287084] using wordTrace_append hprefix tailTrace_5287084
  have hstable : (prefixWord ++ tailWord_5287084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5287084).length < 2 ^ (prefixWord ++ tailWord_5287084).sum := by decide
  have hdescent : baseEnd_5287084 < baseStart_5287084 := by decide
  rcases family_descends (prefixWord ++ tailWord_5287084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5287091 : List Nat := [1, 1, 1, 2, 3, 2, 2, 5, 2, 4]
def baseStart_5287091 : Nat := 118140960795 + 5287091 * 2 ^ 59
def prefixEnd_5287091 : Nat := 4983230072969 + 3 ^ 40 * 5287091 * 2
def baseEnd_5287091 : Nat := 904939649020159655282539

theorem tailTrace_5287091 : CollatzResearch.WordTrace tailWord_5287091 prefixEnd_5287091 904939649020159655282539 := by
  unfold tailWord_5287091
  simp only [CollatzResearch.WordTrace]
  refine ⟨192836050888779745099333127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128557367259186496732888751 192836050888779745099333127)
  ·
    refine ⟨289254076333169617648999691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192836050888779745099333127 289254076333169617648999691)
    ·
      refine ⟨433881114499754426473499537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 289254076333169617648999691 433881114499754426473499537)
      ·
        refine ⟨325410835874815819855124653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 433881114499754426473499537 325410835874815819855124653)
        ·
          refine ⟨122029063453055932445671745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 325410835874815819855124653 122029063453055932445671745)
          ·
            refine ⟨91521797589791949334253809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 122029063453055932445671745 91521797589791949334253809)
            ·
              refine ⟨68641348192343962000690357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91521797589791949334253809 68641348192343962000690357)
              ·
                refine ⟨6435126393032246437564721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 68641348192343962000690357 6435126393032246437564721)
                ·
                  refine ⟨4826344794774184828173541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6435126393032246437564721 4826344794774184828173541)
                  ·
                    refine ⟨904939649020159655282539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4826344794774184828173541 904939649020159655282539)
                    ·
                      rfl

theorem cell23_5287091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 5, 2, 4].length) (baseStart_5287091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5287091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5287091 prefixEnd_5287091 := by exact prefixLift 5287091
  have htrace : WordTrace (prefixWord ++ tailWord_5287091) baseStart_5287091 baseEnd_5287091 := by
    simpa [prefixWord, tailWord_5287091, baseEnd_5287091] using wordTrace_append hprefix tailTrace_5287091
  have hstable : (prefixWord ++ tailWord_5287091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5287091).length < 2 ^ (prefixWord ++ tailWord_5287091).sum := by decide
  have hdescent : baseEnd_5287091 < baseStart_5287091 := by decide
  rcases family_descends (prefixWord ++ tailWord_5287091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5287101 : List Nat := [1, 4, 1, 2, 1, 1, 2, 3, 3, 2, 3]
def baseStart_5287101 : Nat := 118140960795 + 5287101 * 2 ^ 59
def prefixEnd_5287101 : Nat := 4983230072969 + 3 ^ 40 * 5287101 * 2
def baseEnd_5287101 : Nat := 2714824081867023926722571

theorem tailTrace_5287101 : CollatzResearch.WordTrace tailWord_5287101 prefixEnd_5287101 2714824081867023926722571 := by
  unfold tailWord_5287101
  simp only [CollatzResearch.WordTrace]
  refine ⟨192836415618743516807197157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128557610412495677871464771 192836415618743516807197157)
  ·
    refine ⟨36156827928514409401349467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 192836415618743516807197157 36156827928514409401349467)
    ·
      refine ⟨54235241892771614102024201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36156827928514409401349467 54235241892771614102024201)
      ·
        refine ⟨40676431419578710576518151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54235241892771614102024201 40676431419578710576518151)
        ·
          refine ⟨61014647129368065864777227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40676431419578710576518151 61014647129368065864777227)
          ·
            refine ⟨91521970694052098797165841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61014647129368065864777227 91521970694052098797165841)
            ·
              refine ⟨68641478020539074097874381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91521970694052098797165841 68641478020539074097874381)
              ·
                refine ⟨25740554257702152786702893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 68641478020539074097874381 25740554257702152786702893)
                ·
                  refine ⟨9652707846638307295013585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25740554257702152786702893 9652707846638307295013585)
                  ·
                    refine ⟨7239530884978730471260189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9652707846638307295013585 7239530884978730471260189)
                    ·
                      refine ⟨2714824081867023926722571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7239530884978730471260189 2714824081867023926722571)
                      ·
                        rfl

theorem cell23_5287101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 3, 3, 2, 3].length) (baseStart_5287101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5287101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5287101 prefixEnd_5287101 := by exact prefixLift 5287101
  have htrace : WordTrace (prefixWord ++ tailWord_5287101) baseStart_5287101 baseEnd_5287101 := by
    simpa [prefixWord, tailWord_5287101, baseEnd_5287101] using wordTrace_append hprefix tailTrace_5287101
  have hstable : (prefixWord ++ tailWord_5287101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5287101).length < 2 ^ (prefixWord ++ tailWord_5287101).sum := by decide
  have hdescent : baseEnd_5287101 < baseStart_5287101 := by decide
  rcases family_descends (prefixWord ++ tailWord_5287101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5287115 : List Nat := [1, 1, 1, 1, 3, 2, 2, 7, 1, 2, 2]
def baseStart_5287115 : Nat := 118140960795 + 5287115 * 2 ^ 59
def prefixEnd_5287115 : Nat := 4983230072969 + 3 ^ 40 * 5287115 * 2
def baseEnd_5287115 : Nat := 2714831270596186871947507

theorem tailTrace_5287115 : CollatzResearch.WordTrace tailWord_5287115 prefixEnd_5287115 2714831270596186871947507 := by
  unfold tailWord_5287115
  simp only [CollatzResearch.WordTrace]
  refine ⟨192836926240692797198206799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128557950827128531465471199 192836926240692797198206799)
  ·
    refine ⟨289255389361039195797310199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192836926240692797198206799 289255389361039195797310199)
    ·
      refine ⟨433883084041558793695965299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 289255389361039195797310199 433883084041558793695965299)
      ·
        refine ⟨650824626062338190543947949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 433883084041558793695965299 650824626062338190543947949)
        ·
          refine ⟨244059234773376821453980481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 650824626062338190543947949 244059234773376821453980481)
          ·
            refine ⟨183044426080032616090485361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 244059234773376821453980481 183044426080032616090485361)
            ·
              refine ⟨137283319560024462067864021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 183044426080032616090485361 137283319560024462067864021)
              ·
                refine ⟨3217577802188073329715563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 137283319560024462067864021 3217577802188073329715563)
                ·
                  refine ⟨4826366703282109994573345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3217577802188073329715563 4826366703282109994573345)
                  ·
                    refine ⟨3619775027461582495930009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4826366703282109994573345 3619775027461582495930009)
                    ·
                      refine ⟨2714831270596186871947507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3619775027461582495930009 2714831270596186871947507)
                      ·
                        rfl

theorem cell23_5287115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 7, 1, 2, 2].length) (baseStart_5287115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5287115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5287115 prefixEnd_5287115 := by exact prefixLift 5287115
  have htrace : WordTrace (prefixWord ++ tailWord_5287115) baseStart_5287115 baseEnd_5287115 := by
    simpa [prefixWord, tailWord_5287115, baseEnd_5287115] using wordTrace_append hprefix tailTrace_5287115
  have hstable : (prefixWord ++ tailWord_5287115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5287115).length < 2 ^ (prefixWord ++ tailWord_5287115).sum := by decide
  have hdescent : baseEnd_5287115 < baseStart_5287115 := by decide
  rcases family_descends (prefixWord ++ tailWord_5287115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5287118 : List Nat := [4, 1, 1, 1, 5, 1, 2, 1, 1, 1, 5]
def baseStart_5287118 : Nat := 118140960795 + 5287118 * 2 ^ 59
def prefixEnd_5287118 : Nat := 4983230072969 + 3 ^ 40 * 5287118 * 2
def baseEnd_5287118 : Nat := 2714832811038150360209993

theorem tailTrace_5287118 : CollatzResearch.WordTrace tailWord_5287118 prefixEnd_5287118 2714832811038150360209993 := by
  unfold tailWord_5287118
  simp only [CollatzResearch.WordTrace]
  refine ⟨24104629457460241088820751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 128558023773121285807044005 24104629457460241088820751)
  ·
    refine ⟨36156944186190361633231127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24104629457460241088820751 36156944186190361633231127)
    ·
      refine ⟨54235416279285542449846691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36156944186190361633231127 54235416279285542449846691)
      ·
        refine ⟨81353124418928313674770037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54235416279285542449846691 81353124418928313674770037)
        ·
          refine ⟨7626855414274529407009691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 81353124418928313674770037 7626855414274529407009691)
          ·
            refine ⟨11440283121411794110514537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7626855414274529407009691 11440283121411794110514537)
            ·
              refine ⟨8580212341058845582885903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11440283121411794110514537 8580212341058845582885903)
              ·
                refine ⟨12870318511588268374328855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8580212341058845582885903 12870318511588268374328855)
                ·
                  refine ⟨19305477767382402561493283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12870318511588268374328855 19305477767382402561493283)
                  ·
                    refine ⟨28958216651073603842239925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19305477767382402561493283 28958216651073603842239925)
                    ·
                      refine ⟨2714832811038150360209993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28958216651073603842239925 2714832811038150360209993)
                      ·
                        rfl

theorem cell23_5287118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 2, 1, 1, 1, 5].length) (baseStart_5287118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5287118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5287118 prefixEnd_5287118 := by exact prefixLift 5287118
  have htrace : WordTrace (prefixWord ++ tailWord_5287118) baseStart_5287118 baseEnd_5287118 := by
    simpa [prefixWord, tailWord_5287118, baseEnd_5287118] using wordTrace_append hprefix tailTrace_5287118
  have hstable : (prefixWord ++ tailWord_5287118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5287118).length < 2 ^ (prefixWord ++ tailWord_5287118).sum := by decide
  have hdescent : baseEnd_5287118 < baseStart_5287118 := by decide
  rcases family_descends (prefixWord ++ tailWord_5287118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5287126 : List Nat := [5, 2, 1, 2, 2, 1, 3, 2, 1, 1, 3]
def baseStart_5287126 : Nat := 118140960795 + 5287126 * 2 ^ 59
def prefixEnd_5287126 : Nat := 4983230072969 + 3 ^ 40 * 5287126 * 2
def baseEnd_5287126 : Nat := 2714836918883386328909957

theorem tailTrace_5287126 : CollatzResearch.WordTrace tailWord_5287126 prefixEnd_5287126 2714836918883386328909957 := by
  unfold tailWord_5287126
  simp only [CollatzResearch.WordTrace]
  refine ⟨12052332965228309129803577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 128558218295768630717904821 12052332965228309129803577)
  ·
    refine ⟨9039249723921231847352683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12052332965228309129803577 9039249723921231847352683)
    ·
      refine ⟨13558874585881847771029025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9039249723921231847352683 13558874585881847771029025)
      ·
        refine ⟨10169155939411385828271769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13558874585881847771029025 10169155939411385828271769)
        ·
          refine ⟨7626866954558539371203827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10169155939411385828271769 7626866954558539371203827)
          ·
            refine ⟨11440300431837809056805741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7626866954558539371203827 11440300431837809056805741)
            ·
              refine ⟨4290112661939178396302153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11440300431837809056805741 4290112661939178396302153)
              ·
                refine ⟨3217584496454383797226615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4290112661939178396302153 3217584496454383797226615)
                ·
                  refine ⟨4826376744681575695839923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3217584496454383797226615 4826376744681575695839923)
                  ·
                    refine ⟨7239565117022363543759885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4826376744681575695839923 7239565117022363543759885)
                    ·
                      refine ⟨2714836918883386328909957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7239565117022363543759885 2714836918883386328909957)
                      ·
                        rfl

theorem cell23_5287126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 3, 2, 1, 1, 3].length) (baseStart_5287126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5287126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5287126 prefixEnd_5287126 := by exact prefixLift 5287126
  have htrace : WordTrace (prefixWord ++ tailWord_5287126) baseStart_5287126 baseEnd_5287126 := by
    simpa [prefixWord, tailWord_5287126, baseEnd_5287126] using wordTrace_append hprefix tailTrace_5287126
  have hstable : (prefixWord ++ tailWord_5287126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5287126).length < 2 ^ (prefixWord ++ tailWord_5287126).sum := by decide
  have hdescent : baseEnd_5287126 < baseStart_5287126 := by decide
  rcases family_descends (prefixWord ++ tailWord_5287126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5287131 : List Nat := [1, 1, 1, 1, 1, 1, 1, 4, 8, 1, 3]
def baseStart_5287131 : Nat := 118140960795 + 5287131 * 2 ^ 59
def prefixEnd_5287131 : Nat := 4983230072969 + 3 ^ 40 * 5287131 * 2
def baseEnd_5287131 : Nat := 2714839486286658809347433

theorem tailTrace_5287131 : CollatzResearch.WordTrace tailWord_5287131 prefixEnd_5287131 2714839486286658809347433 := by
  unfold tailWord_5287131
  simp only [CollatzResearch.WordTrace]
  refine ⟨192837509808634831930789247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128558339872423221287192831 192837509808634831930789247)
  ·
    refine ⟨289256264712952247896183871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192837509808634831930789247 289256264712952247896183871)
    ·
      refine ⟨433884397069428371844275807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 289256264712952247896183871 433884397069428371844275807)
      ·
        refine ⟨650826595604142557766413711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 433884397069428371844275807 650826595604142557766413711)
        ·
          refine ⟨976239893406213836649620567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 650826595604142557766413711 976239893406213836649620567)
          ·
            refine ⟨1464359840109320754974430851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 976239893406213836649620567 1464359840109320754974430851)
            ·
              refine ⟨2196539760163981132461646277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1464359840109320754974430851 2196539760163981132461646277)
              ·
                refine ⟨411851205030746462336558677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2196539760163981132461646277 411851205030746462336558677)
                ·
                  refine ⟨4826381308954060105506547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 411851205030746462336558677 4826381308954060105506547)
                  ·
                    refine ⟨7239571963431090158259821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4826381308954060105506547 7239571963431090158259821)
                    ·
                      refine ⟨2714839486286658809347433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7239571963431090158259821 2714839486286658809347433)
                      ·
                        rfl

theorem cell23_5287131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 8, 1, 3].length) (baseStart_5287131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5287131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5287131 prefixEnd_5287131 := by exact prefixLift 5287131
  have htrace : WordTrace (prefixWord ++ tailWord_5287131) baseStart_5287131 baseEnd_5287131 := by
    simpa [prefixWord, tailWord_5287131, baseEnd_5287131] using wordTrace_append hprefix tailTrace_5287131
  have hstable : (prefixWord ++ tailWord_5287131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5287131).length < 2 ^ (prefixWord ++ tailWord_5287131).sum := by decide
  have hdescent : baseEnd_5287131 < baseStart_5287131 := by decide
  rcases family_descends (prefixWord ++ tailWord_5287131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5287191 : List Nat := [1, 1, 3, 4, 1, 1, 1, 1, 1, 6, 3]
def baseStart_5287191 : Nat := 118140960795 + 5287191 * 2 ^ 59
def prefixEnd_5287191 : Nat := 4983230072969 + 3 ^ 40 * 5287191 * 2
def baseEnd_5287191 : Nat := 2714870295125928574597157

theorem tailTrace_5287191 : CollatzResearch.WordTrace tailWord_5287191 prefixEnd_5287191 2714870295125928574597157 := by
  unfold tailWord_5287191
  simp only [CollatzResearch.WordTrace]
  refine ⟨192839698188417462177973427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128559798792278308118648951 192839698188417462177973427)
  ·
    refine ⟨289259547282626193266960141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192839698188417462177973427 289259547282626193266960141)
    ·
      refine ⟨108472330230984822475110053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 289259547282626193266960141 108472330230984822475110053)
      ·
        refine ⟨20338561918309654214083135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 108472330230984822475110053 20338561918309654214083135)
        ·
          refine ⟨30507842877464481321124703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20338561918309654214083135 30507842877464481321124703)
          ·
            refine ⟨45761764316196721981687055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30507842877464481321124703 45761764316196721981687055)
            ·
              refine ⟨68642646474295082972530583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45761764316196721981687055 68642646474295082972530583)
              ·
                refine ⟨102963969711442624458795875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68642646474295082972530583 102963969711442624458795875)
                ·
                  refine ⟨154445954567163936688193813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 102963969711442624458795875 154445954567163936688193813)
                  ·
                    refine ⟨7239654120335809532259085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 154445954567163936688193813 7239654120335809532259085)
                    ·
                      refine ⟨2714870295125928574597157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7239654120335809532259085 2714870295125928574597157)
                      ·
                        rfl

theorem cell23_5287191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 1, 1, 6, 3].length) (baseStart_5287191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5287191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5287191 prefixEnd_5287191 := by exact prefixLift 5287191
  have htrace : WordTrace (prefixWord ++ tailWord_5287191) baseStart_5287191 baseEnd_5287191 := by
    simpa [prefixWord, tailWord_5287191, baseEnd_5287191] using wordTrace_append hprefix tailTrace_5287191
  have hstable : (prefixWord ++ tailWord_5287191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5287191).length < 2 ^ (prefixWord ++ tailWord_5287191).sum := by decide
  have hdescent : baseEnd_5287191 < baseStart_5287191 := by decide
  rcases family_descends (prefixWord ++ tailWord_5287191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5287205 : List Nat := [1, 3, 1, 2, 4, 2, 2, 1, 1, 4, 2]
def baseStart_5287205 : Nat := 118140960795 + 5287205 * 2 ^ 59
def prefixEnd_5287205 : Nat := 4983230072969 + 3 ^ 40 * 5287205 * 2
def baseEnd_5287205 : Nat := 2714877483855091519822093

theorem tailTrace_5287205 : CollatzResearch.WordTrace tailWord_5287205 prefixEnd_5287205 2714877483855091519822093 := by
  unfold tailWord_5287205
  simp only [CollatzResearch.WordTrace]
  refine ⟨192840208810366742568983069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128560139206911161712655379 192840208810366742568983069)
  ·
    refine ⟨72315078303887528463368651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 192840208810366742568983069 72315078303887528463368651)
    ·
      refine ⟨108472617455831292695052977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72315078303887528463368651 108472617455831292695052977)
      ·
        refine ⟨81354463091873469521289733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108472617455831292695052977 81354463091873469521289733)
        ·
          refine ⟨15253961829726275535241825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 81354463091873469521289733 15253961829726275535241825)
          ·
            refine ⟨11440471372294706651431369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15253961829726275535241825 11440471372294706651431369)
            ·
              refine ⟨8580353529221029988573527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11440471372294706651431369 8580353529221029988573527)
              ·
                refine ⟨12870530293831544982860291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8580353529221029988573527 12870530293831544982860291)
                ·
                  refine ⟨19305795440747317474290437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12870530293831544982860291 19305795440747317474290437)
                  ·
                    refine ⟨3619836645140122026429457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19305795440747317474290437 3619836645140122026429457)
                    ·
                      refine ⟨2714877483855091519822093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3619836645140122026429457 2714877483855091519822093)
                      ·
                        rfl

theorem cell23_5287205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 2, 1, 1, 4, 2].length) (baseStart_5287205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5287205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5287205 prefixEnd_5287205 := by exact prefixLift 5287205
  have htrace : WordTrace (prefixWord ++ tailWord_5287205) baseStart_5287205 baseEnd_5287205 := by
    simpa [prefixWord, tailWord_5287205, baseEnd_5287205] using wordTrace_append hprefix tailTrace_5287205
  have hstable : (prefixWord ++ tailWord_5287205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5287205).length < 2 ^ (prefixWord ++ tailWord_5287205).sum := by decide
  have hdescent : baseEnd_5287205 < baseStart_5287205 := by decide
  rcases family_descends (prefixWord ++ tailWord_5287205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5287228 : List Nat := [2, 2, 2, 2, 1, 3, 1, 5, 5]
def baseStart_5287228 : Nat := 118140960795 + 5287228 * 2 ^ 59
def prefixEnd_5287228 : Nat := 4983230072969 + 3 ^ 40 * 5287228 * 2
def baseEnd_5287228 : Nat := 301654365990016103314943

theorem tailTrace_5287228 : CollatzResearch.WordTrace tailWord_5287228 prefixEnd_5287228 301654365990016103314943 := by
  unfold tailWord_5287228
  simp only [CollatzResearch.WordTrace]
  refine ⟨96420523844641708748535169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128560698459522278331380225 96420523844641708748535169)
  ·
    refine ⟨72315392883481281561401377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96420523844641708748535169 72315392883481281561401377)
    ·
      refine ⟨54236544662610961171051033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72315392883481281561401377 54236544662610961171051033)
      ·
        refine ⟨40677408496958220878288275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54236544662610961171051033 40677408496958220878288275)
        ·
          refine ⟨61016112745437331317432413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40677408496958220878288275 61016112745437331317432413)
          ·
            refine ⟨22881042279538999244037155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61016112745437331317432413 22881042279538999244037155)
            ·
              refine ⟨34321563419308498866055733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22881042279538999244037155 34321563419308498866055733)
              ·
                refine ⟨3217646570560171768692725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34321563419308498866055733 3217646570560171768692725)
                ·
                  refine ⟨301654365990016103314943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3217646570560171768692725 301654365990016103314943)
                  ·
                    rfl

theorem cell23_5287228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 5, 5].length) (baseStart_5287228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5287228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5287228 prefixEnd_5287228 := by exact prefixLift 5287228
  have htrace : WordTrace (prefixWord ++ tailWord_5287228) baseStart_5287228 baseEnd_5287228 := by
    simpa [prefixWord, tailWord_5287228, baseEnd_5287228] using wordTrace_append hprefix tailTrace_5287228
  have hstable : (prefixWord ++ tailWord_5287228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5287228).length < 2 ^ (prefixWord ++ tailWord_5287228).sum := by decide
  have hdescent : baseEnd_5287228 < baseStart_5287228 := by decide
  rcases family_descends (prefixWord ++ tailWord_5287228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5287241 : List Nat := [1, 2, 1, 1, 2, 3, 2, 4, 2, 5]
def baseStart_5287241 : Nat := 118140960795 + 5287241 * 2 ^ 59
def prefixEnd_5287241 : Nat := 4983230072969 + 3 ^ 40 * 5287241 * 2
def baseEnd_5287241 : Nat := 904965323052884459657309

theorem tailTrace_5287241 : CollatzResearch.WordTrace tailWord_5287241 prefixEnd_5287241 904965323052884459657309 := by
  unfold tailWord_5287241
  simp only [CollatzResearch.WordTrace]
  refine ⟨192841521838236320717293577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128561014558824213811529051 192841521838236320717293577)
  ·
    refine ⟨144631141378677240537970183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192841521838236320717293577 144631141378677240537970183)
    ·
      refine ⟨216946712068015860806955275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144631141378677240537970183 216946712068015860806955275)
      ·
        refine ⟨325420068102023791210432913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 216946712068015860806955275 325420068102023791210432913)
        ·
          refine ⟨244065051076517843407824685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 325420068102023791210432913 244065051076517843407824685)
          ·
            refine ⟨91524394153694191277934257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 244065051076517843407824685 91524394153694191277934257)
            ·
              refine ⟨68643295615270643458450693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91524394153694191277934257 68643295615270643458450693)
              ·
                refine ⟨12870617927863245648459505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 68643295615270643458450693 12870617927863245648459505)
                ·
                  refine ⟨9652963445897434236344629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12870617927863245648459505 9652963445897434236344629)
                  ·
                    refine ⟨904965323052884459657309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9652963445897434236344629 904965323052884459657309)
                    ·
                      rfl

theorem cell23_5287241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 4, 2, 5].length) (baseStart_5287241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5287241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5287241 prefixEnd_5287241 := by exact prefixLift 5287241
  have htrace : WordTrace (prefixWord ++ tailWord_5287241) baseStart_5287241 baseEnd_5287241 := by
    simpa [prefixWord, tailWord_5287241, baseEnd_5287241] using wordTrace_append hprefix tailTrace_5287241
  have hstable : (prefixWord ++ tailWord_5287241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5287241).length < 2 ^ (prefixWord ++ tailWord_5287241).sum := by decide
  have hdescent : baseEnd_5287241 < baseStart_5287241 := by decide
  rcases family_descends (prefixWord ++ tailWord_5287241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5287301 : List Nat := [1, 3, 1, 1, 3, 1, 4, 1, 8]
def baseStart_5287301 : Nat := 118140960795 + 5287301 * 2 ^ 59
def prefixEnd_5287301 : Nat := 4983230072969 + 3 ^ 40 * 5287301 * 2
def baseEnd_5287301 : Nat := 301658530888658127135739

theorem tailTrace_5287301 : CollatzResearch.WordTrace tailWord_5287301 prefixEnd_5287301 301658530888658127135739 := by
  unfold tailWord_5287301
  simp only [CollatzResearch.WordTrace]
  refine ⟨192843710218018950964477757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128562473478679300642985171 192843710218018950964477757)
  ·
    refine ⟨72316391331757106611679159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 192843710218018950964477757 72316391331757106611679159)
    ·
      refine ⟨108474586997635659917518739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72316391331757106611679159 108474586997635659917518739)
      ·
        refine ⟨162711880496453489876278109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108474586997635659917518739 162711880496453489876278109)
        ·
          refine ⟨61016955186170058703604291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 162711880496453489876278109 61016955186170058703604291)
          ·
            refine ⟨91525432779255088055406437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61016955186170058703604291 91525432779255088055406437)
            ·
              refine ⟨17161018646110329010388707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 91525432779255088055406437 17161018646110329010388707)
              ·
                refine ⟨25741527969165493515583061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17161018646110329010388707 25741527969165493515583061)
                ·
                  refine ⟨301658530888658127135739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25741527969165493515583061 301658530888658127135739)
                  ·
                    rfl

theorem cell23_5287301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 4, 1, 8].length) (baseStart_5287301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5287301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5287301 prefixEnd_5287301 := by exact prefixLift 5287301
  have htrace : WordTrace (prefixWord ++ tailWord_5287301) baseStart_5287301 baseEnd_5287301 := by
    simpa [prefixWord, tailWord_5287301, baseEnd_5287301] using wordTrace_append hprefix tailTrace_5287301
  have hstable : (prefixWord ++ tailWord_5287301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5287301).length < 2 ^ (prefixWord ++ tailWord_5287301).sum := by decide
  have hdescent : baseEnd_5287301 < baseStart_5287301 := by decide
  rcases family_descends (prefixWord ++ tailWord_5287301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5287356 : List Nat := [2, 2, 2, 4, 2, 2, 2, 2, 1, 4]
def baseStart_5287356 : Nat := 118140960795 + 5287356 * 2 ^ 59
def prefixEnd_5287356 : Nat := 4983230072969 + 3 ^ 40 * 5287356 * 2
def baseEnd_5287356 : Nat := 904985006477973476344633

theorem tailTrace_5287356 : CollatzResearch.WordTrace tailWord_5287356 prefixEnd_5287356 904985006477973476344633 := by
  unfold tailWord_5287356
  simp only [CollatzResearch.WordTrace]
  refine ⟨96422858116409847678864961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128563810821879796905153281 96422858116409847678864961)
  ·
    refine ⟨72317143587307385759148721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96422858116409847678864961 72317143587307385759148721)
    ·
      refine ⟨54237857690480539319361541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72317143587307385759148721 54237857690480539319361541)
      ·
        refine ⟨10169598316965101122380289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54237857690480539319361541 10169598316965101122380289)
        ·
          refine ⟨7627198737723825841785217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10169598316965101122380289 7627198737723825841785217)
          ·
            refine ⟨5720399053292869381338913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7627198737723825841785217 5720399053292869381338913)
            ·
              refine ⟨4290299289969652036004185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5720399053292869381338913 4290299289969652036004185)
              ·
                refine ⟨3217724467477239027003139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4290299289969652036004185 3217724467477239027003139)
                ·
                  refine ⟨4826586701215858540504709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3217724467477239027003139 4826586701215858540504709)
                  ·
                    refine ⟨904985006477973476344633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4826586701215858540504709 904985006477973476344633)
                    ·
                      rfl

theorem cell23_5287356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 2, 2, 1, 4].length) (baseStart_5287356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5287356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5287356 prefixEnd_5287356 := by exact prefixLift 5287356
  have htrace : WordTrace (prefixWord ++ tailWord_5287356) baseStart_5287356 baseEnd_5287356 := by
    simpa [prefixWord, tailWord_5287356, baseEnd_5287356] using wordTrace_append hprefix tailTrace_5287356
  have hstable : (prefixWord ++ tailWord_5287356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5287356).length < 2 ^ (prefixWord ++ tailWord_5287356).sum := by decide
  have hdescent : baseEnd_5287356 < baseStart_5287356 := by decide
  rcases family_descends (prefixWord ++ tailWord_5287356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5287368 : List Nat := [2, 1, 3, 1, 3, 1, 1, 1, 5, 1, 4]
def baseStart_5287368 : Nat := 118140960795 + 5287368 * 2 ^ 59
def prefixEnd_5287368 : Nat := 4983230072969 + 3 ^ 40 * 5287368 * 2
def baseEnd_5287368 : Nat := 2714961181201774382083843

theorem tailTrace_5287368 : CollatzResearch.WordTrace tailWord_5287368 prefixEnd_5287368 2714961181201774382083843 := by
  unfold tailWord_5287368
  simp only [CollatzResearch.WordTrace]
  refine ⟨96423076954388110703583379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128564102605850814271444505 96423076954388110703583379)
  ·
    refine ⟨144634615431582166055375069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96423076954388110703583379 144634615431582166055375069)
    ·
      refine ⟨54237980786843312270765651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 144634615431582166055375069 54237980786843312270765651)
      ·
        refine ⟨81356971180264968406148477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54237980786843312270765651 81356971180264968406148477)
        ·
          refine ⟨30508864192599363152305679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81356971180264968406148477 30508864192599363152305679)
          ·
            refine ⟨45763296288899044728458519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30508864192599363152305679 45763296288899044728458519)
            ·
              refine ⟨68644944433348567092687779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45763296288899044728458519 68644944433348567092687779)
              ·
                refine ⟨102967416650022850639031669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68644944433348567092687779 102967416650022850639031669)
                ·
                  refine ⟨9653195310939642247409219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 102967416650022850639031669 9653195310939642247409219)
                  ·
                    refine ⟨14479792966409463371113829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9653195310939642247409219 14479792966409463371113829)
                    ·
                      refine ⟨2714961181201774382083843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14479792966409463371113829 2714961181201774382083843)
                      ·
                        rfl

theorem cell23_5287368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 1, 5, 1, 4].length) (baseStart_5287368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5287368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5287368 prefixEnd_5287368 := by exact prefixLift 5287368
  have htrace : WordTrace (prefixWord ++ tailWord_5287368) baseStart_5287368 baseEnd_5287368 := by
    simpa [prefixWord, tailWord_5287368, baseEnd_5287368] using wordTrace_append hprefix tailTrace_5287368
  have hstable : (prefixWord ++ tailWord_5287368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5287368).length < 2 ^ (prefixWord ++ tailWord_5287368).sum := by decide
  have hdescent : baseEnd_5287368 < baseStart_5287368 := by decide
  rcases family_descends (prefixWord ++ tailWord_5287368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5287389 : List Nat := [1, 4, 3, 1, 1, 4, 1, 1, 2, 3, 2]
def baseStart_5287389 : Nat := 118140960795 + 5287389 * 2 ^ 59
def prefixEnd_5287389 : Nat := 4983230072969 + 3 ^ 40 * 5287389 * 2
def baseEnd_5287389 : Nat := 2714971964295518799921247

theorem tailTrace_5287389 : CollatzResearch.WordTrace tailWord_5287389 prefixEnd_5287389 2714971964295518799921247 := by
  unfold tailWord_5287389
  simp only [CollatzResearch.WordTrace]
  refine ⟨192846919841700141993681221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128564613227800094662454147 192846919841700141993681221)
  ·
    refine ⟨36158797470318776623815229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 192846919841700141993681221 36158797470318776623815229)
    ·
      refine ⟨13559549051369541233930711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36158797470318776623815229 13559549051369541233930711)
      ·
        refine ⟨20339323577054311850896067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13559549051369541233930711 20339323577054311850896067)
        ·
          refine ⟨30508985365581467776344101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20339323577054311850896067 30508985365581467776344101)
          ·
            refine ⟨5720434756046525208064519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30508985365581467776344101 5720434756046525208064519)
            ·
              refine ⟨8580652134069787812096779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5720434756046525208064519 8580652134069787812096779)
              ·
                refine ⟨12870978201104681718145169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8580652134069787812096779 12870978201104681718145169)
                ·
                  refine ⟨9653233650828511288608877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12870978201104681718145169 9653233650828511288608877)
                  ·
                    refine ⟨3619962619060691733228329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9653233650828511288608877 3619962619060691733228329)
                    ·
                      refine ⟨2714971964295518799921247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3619962619060691733228329 2714971964295518799921247)
                      ·
                        rfl

theorem cell23_5287389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 1, 1, 2, 3, 2].length) (baseStart_5287389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5287389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5287389 prefixEnd_5287389 := by exact prefixLift 5287389
  have htrace : WordTrace (prefixWord ++ tailWord_5287389) baseStart_5287389 baseEnd_5287389 := by
    simpa [prefixWord, tailWord_5287389, baseEnd_5287389] using wordTrace_append hprefix tailTrace_5287389
  have hstable : (prefixWord ++ tailWord_5287389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5287389).length < 2 ^ (prefixWord ++ tailWord_5287389).sum := by decide
  have hdescent : baseEnd_5287389 < baseStart_5287389 := by decide
  rcases family_descends (prefixWord ++ tailWord_5287389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5287401 : List Nat := [1, 2, 1, 1, 1, 2, 1, 2, 1, 4, 7]
def baseStart_5287401 : Nat := 118140960795 + 5287401 * 2 ^ 59
def prefixEnd_5287401 : Nat := 4983230072969 + 3 ^ 40 * 5287401 * 2
def baseEnd_5287401 : Nat := 2714978126063372752971191

theorem tailTrace_5287401 : CollatzResearch.WordTrace tailWord_5287401 prefixEnd_5287401 2714978126063372752971191 := by
  unfold tailWord_5287401
  simp only [CollatzResearch.WordTrace]
  refine ⟨192847357517656668043118057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128564905011771112028745371 192847357517656668043118057)
  ·
    refine ⟨144635518138242501032338543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192847357517656668043118057 144635518138242501032338543)
    ·
      refine ⟨216953277207363751548507815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144635518138242501032338543 216953277207363751548507815)
      ·
        refine ⟨325429915811045627322761723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 216953277207363751548507815 325429915811045627322761723)
        ·
          refine ⟨488144873716568440984142585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 325429915811045627322761723 488144873716568440984142585)
          ·
            refine ⟨366108655287426330738106939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 488144873716568440984142585 366108655287426330738106939)
            ·
              refine ⟨549162982931139496107160409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 366108655287426330738106939 549162982931139496107160409)
              ·
                refine ⟨411872237198354622080370307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 549162982931139496107160409 411872237198354622080370307)
                ·
                  refine ⟨617808355797531933120555461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 411872237198354622080370307 617808355797531933120555461)
                  ·
                    refine ⟨115839066712037237460104149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 617808355797531933120555461 115839066712037237460104149)
                    ·
                      refine ⟨2714978126063372752971191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 115839066712037237460104149 2714978126063372752971191)
                      ·
                        rfl

theorem cell23_5287401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 4, 7].length) (baseStart_5287401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5287401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5287401 prefixEnd_5287401 := by exact prefixLift 5287401
  have htrace : WordTrace (prefixWord ++ tailWord_5287401) baseStart_5287401 baseEnd_5287401 := by
    simpa [prefixWord, tailWord_5287401, baseEnd_5287401] using wordTrace_append hprefix tailTrace_5287401
  have hstable : (prefixWord ++ tailWord_5287401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5287401).length < 2 ^ (prefixWord ++ tailWord_5287401).sum := by decide
  have hdescent : baseEnd_5287401 < baseStart_5287401 := by decide
  rcases family_descends (prefixWord ++ tailWord_5287401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5287402 : List Nat := [3, 1, 3, 1, 4, 1, 1, 3, 1, 1, 4]
def baseStart_5287402 : Nat := 118140960795 + 5287402 * 2 ^ 59
def prefixEnd_5287402 : Nat := 4983230072969 + 3 ^ 40 * 5287402 * 2
def baseEnd_5287402 : Nat := 2714978639544027249058687

theorem tailTrace_5287402 : CollatzResearch.WordTrace tailWord_5287402 prefixEnd_5287402 2714978639544027249058687 := by
  unfold tailWord_5287402
  simp only [CollatzResearch.WordTrace]
  refine ⟨48211848497663261303476115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128564929327102030142602973 48211848497663261303476115)
  ·
    refine ⟨72317772746494891955214173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48211848497663261303476115 72317772746494891955214173)
    ·
      refine ⟨27119164779935584483205315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72317772746494891955214173 27119164779935584483205315)
      ·
        refine ⟨40678747169903376724807973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27119164779935584483205315 40678747169903376724807973)
        ·
          refine ⟨7627265094356883135901495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40678747169903376724807973 7627265094356883135901495)
          ·
            refine ⟨11440897641535324703852243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7627265094356883135901495 11440897641535324703852243)
            ·
              refine ⟨17161346462302987055778365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11440897641535324703852243 17161346462302987055778365)
              ·
                refine ⟨6435504923363620145916887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17161346462302987055778365 6435504923363620145916887)
                ·
                  refine ⟨9653257385045430218875331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6435504923363620145916887 9653257385045430218875331)
                  ·
                    refine ⟨14479886077568145328312997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9653257385045430218875331 14479886077568145328312997)
                    ·
                      refine ⟨2714978639544027249058687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14479886077568145328312997 2714978639544027249058687)
                      ·
                        rfl

theorem cell23_5287402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 1, 3, 1, 1, 4].length) (baseStart_5287402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5287402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5287402 prefixEnd_5287402 := by exact prefixLift 5287402
  have htrace : WordTrace (prefixWord ++ tailWord_5287402) baseStart_5287402 baseEnd_5287402 := by
    simpa [prefixWord, tailWord_5287402, baseEnd_5287402] using wordTrace_append hprefix tailTrace_5287402
  have hstable : (prefixWord ++ tailWord_5287402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5287402).length < 2 ^ (prefixWord ++ tailWord_5287402).sum := by decide
  have hdescent : baseEnd_5287402 < baseStart_5287402 := by decide
  rcases family_descends (prefixWord ++ tailWord_5287402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5287488 : List Nat := [2, 1, 1, 2, 2, 2, 1, 3, 1, 4, 4]
def baseStart_5287488 : Nat := 118140960795 + 5287488 * 2 ^ 59
def prefixEnd_5287488 : Nat := 4983230072969 + 3 ^ 40 * 5287488 * 2
def baseEnd_5287488 : Nat := 2715022798880313912583291

theorem tailTrace_5287488 : CollatzResearch.WordTrace tailWord_5287488 prefixEnd_5287488 2715022798880313912583291 := by
  unfold tailWord_5287488
  simp only [CollatzResearch.WordTrace]
  refine ⟨96425265334170740950767559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128567020445560987934356745 96425265334170740950767559)
  ·
    refine ⟨144637898001256111426151339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96425265334170740950767559 144637898001256111426151339)
    ·
      refine ⟨216956847001884167139227009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144637898001256111426151339 216956847001884167139227009)
      ·
        refine ⟨162717635251413125354420257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 216956847001884167139227009 162717635251413125354420257)
        ·
          refine ⟨122038226438559844015815193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 162717635251413125354420257 122038226438559844015815193)
          ·
            refine ⟨91528669828919883011861395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 122038226438559844015815193 91528669828919883011861395)
            ·
              refine ⟨137293004743379824517792093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91528669828919883011861395 137293004743379824517792093)
              ·
                refine ⟨51484876778767434194172035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 137293004743379824517792093 51484876778767434194172035)
                ·
                  refine ⟨77227315168151151291258053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51484876778767434194172035 77227315168151151291258053)
                  ·
                    refine ⟨14480121594028340867110885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 77227315168151151291258053 14480121594028340867110885)
                    ·
                      refine ⟨2715022798880313912583291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14480121594028340867110885 2715022798880313912583291)
                      ·
                        rfl

theorem cell23_5287488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 3, 1, 4, 4].length) (baseStart_5287488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5287488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5287488 prefixEnd_5287488 := by exact prefixLift 5287488
  have htrace : WordTrace (prefixWord ++ tailWord_5287488) baseStart_5287488 baseEnd_5287488 := by
    simpa [prefixWord, tailWord_5287488, baseEnd_5287488] using wordTrace_append hprefix tailTrace_5287488
  have hstable : (prefixWord ++ tailWord_5287488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5287488).length < 2 ^ (prefixWord ++ tailWord_5287488).sum := by decide
  have hdescent : baseEnd_5287488 < baseStart_5287488 := by decide
  rcases family_descends (prefixWord ++ tailWord_5287488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5287498 : List Nat := [3, 1, 2, 1, 1, 3, 2, 1, 9]
def baseStart_5287498 : Nat := 118140960795 + 5287498 * 2 ^ 59
def prefixEnd_5287498 : Nat := 4983230072969 + 3 ^ 40 * 5287498 * 2
def baseEnd_5287498 : Nat := 301669770409650985939805

theorem tailTrace_5287498 : CollatzResearch.WordTrace tailWord_5287498 prefixEnd_5287498 301669770409650985939805 := by
  unfold tailWord_5287498
  simp only [CollatzResearch.WordTrace]
  refine ⟨48212723849576313402349787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128567263598870169072932765 48212723849576313402349787)
  ·
    refine ⟨72319085774364470103524681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48212723849576313402349787 72319085774364470103524681)
    ·
      refine ⟨54239314330773352577643511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72319085774364470103524681 54239314330773352577643511)
      ·
        refine ⟨81358971496160028866465267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54239314330773352577643511 81358971496160028866465267)
        ·
          refine ⟨122038457244240043299697901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81358971496160028866465267 122038457244240043299697901)
          ·
            refine ⟨45764421466590016237386713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 122038457244240043299697901 45764421466590016237386713)
            ·
              refine ⟨34323316099942512178040035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45764421466590016237386713 34323316099942512178040035)
              ·
                refine ⟨51484974149913768267060053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34323316099942512178040035 51484974149913768267060053)
                ·
                  refine ⟨301669770409650985939805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 51484974149913768267060053 301669770409650985939805)
                  ·
                    rfl

theorem cell23_5287498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 1, 9].length) (baseStart_5287498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5287498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5287498 prefixEnd_5287498 := by exact prefixLift 5287498
  have htrace : WordTrace (prefixWord ++ tailWord_5287498) baseStart_5287498 baseEnd_5287498 := by
    simpa [prefixWord, tailWord_5287498, baseEnd_5287498] using wordTrace_append hprefix tailTrace_5287498
  have hstable : (prefixWord ++ tailWord_5287498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5287498).length < 2 ^ (prefixWord ++ tailWord_5287498).sum := by decide
  have hdescent : baseEnd_5287498 < baseStart_5287498 := by decide
  rcases family_descends (prefixWord ++ tailWord_5287498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5287542 : List Nat := [5, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3]
def baseStart_5287542 : Nat := 118140960795 + 5287542 * 2 ^ 59
def prefixEnd_5287542 : Nat := 4983230072969 + 3 ^ 40 * 5287542 * 2
def baseEnd_5287542 : Nat := 2715050526835656701308043

theorem tailTrace_5287542 : CollatzResearch.WordTrace tailWord_5287542 prefixEnd_5287542 2715050526835656701308043 := by
  unfold tailWord_5287542
  simp only [CollatzResearch.WordTrace]
  refine ⟨12053281263134115570250055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 128568333473430566082667253 12053281263134115570250055)
  ·
    refine ⟨18079921894701173355375083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12053281263134115570250055 18079921894701173355375083)
    ·
      refine ⟨27119882842051760033062625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18079921894701173355375083 27119882842051760033062625)
      ·
        refine ⟨20339912131538820024796969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27119882842051760033062625 20339912131538820024796969)
        ·
          refine ⟨15254934098654115018597727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20339912131538820024796969 15254934098654115018597727)
          ·
            refine ⟨22882401147981172527896591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15254934098654115018597727 22882401147981172527896591)
            ·
              refine ⟨34323601721971758791844887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22882401147981172527896591 34323601721971758791844887)
              ·
                refine ⟨51485402582957638187767331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34323601721971758791844887 51485402582957638187767331)
                ·
                  refine ⟨77228103874436457281650997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51485402582957638187767331 77228103874436457281650997)
                  ·
                    refine ⟨7240134738228417870154781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 77228103874436457281650997 7240134738228417870154781)
                    ·
                      refine ⟨2715050526835656701308043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7240134738228417870154781 2715050526835656701308043)
                      ·
                        rfl

theorem cell23_5287542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3].length) (baseStart_5287542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5287542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5287542 prefixEnd_5287542 := by exact prefixLift 5287542
  have htrace : WordTrace (prefixWord ++ tailWord_5287542) baseStart_5287542 baseEnd_5287542 := by
    simpa [prefixWord, tailWord_5287542, baseEnd_5287542] using wordTrace_append hprefix tailTrace_5287542
  have hstable : (prefixWord ++ tailWord_5287542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5287542).length < 2 ^ (prefixWord ++ tailWord_5287542).sum := by decide
  have hdescent : baseEnd_5287542 < baseStart_5287542 := by decide
  rcases family_descends (prefixWord ++ tailWord_5287542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5287562 : List Nat := [3, 1, 2, 3, 2, 1, 3, 1, 2, 5]
def baseStart_5287562 : Nat := 118140960795 + 5287562 * 2 ^ 59
def prefixEnd_5287562 : Nat := 4983230072969 + 3 ^ 40 * 5287562 * 2
def baseEnd_5287562 : Nat := 905020265482915541019317

theorem tailTrace_5287562 : CollatzResearch.WordTrace tailWord_5287562 prefixEnd_5287562 905020265482915541019317 := by
  unfold tailWord_5287562
  simp only [CollatzResearch.WordTrace]
  refine ⟨48213307417518348134932235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128568819780048928359819293 48213307417518348134932235)
  ·
    refine ⟨72319961126277522202398353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48213307417518348134932235 72319961126277522202398353)
    ·
      refine ⟨54239970844708141651798765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72319961126277522202398353 54239970844708141651798765)
      ·
        refine ⟨20339989066765553119424537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54239970844708141651798765 20339989066765553119424537)
        ·
          refine ⟨15254991800074164839568403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20339989066765553119424537 15254991800074164839568403)
          ·
            refine ⟨22882487700111247259352605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15254991800074164839568403 22882487700111247259352605)
            ·
              refine ⟨8580932887541717722257227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22882487700111247259352605 8580932887541717722257227)
              ·
                refine ⟨12871399331312576583385841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8580932887541717722257227 12871399331312576583385841)
                ·
                  refine ⟨9653549498484432437539381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12871399331312576583385841 9653549498484432437539381)
                  ·
                    refine ⟨905020265482915541019317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9653549498484432437539381 905020265482915541019317)
                    ·
                      rfl

theorem cell23_5287562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 3, 1, 2, 5].length) (baseStart_5287562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5287562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5287562 prefixEnd_5287562 := by exact prefixLift 5287562
  have htrace : WordTrace (prefixWord ++ tailWord_5287562) baseStart_5287562 baseEnd_5287562 := by
    simpa [prefixWord, tailWord_5287562, baseEnd_5287562] using wordTrace_append hprefix tailTrace_5287562
  have hstable : (prefixWord ++ tailWord_5287562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5287562).length < 2 ^ (prefixWord ++ tailWord_5287562).sum := by decide
  have hdescent : baseEnd_5287562 < baseStart_5287562 := by decide
  rcases family_descends (prefixWord ++ tailWord_5287562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5287615 : List Nat := [1, 1, 2, 2, 2, 3, 1, 1, 2, 5, 3]
def baseStart_5287615 : Nat := 118140960795 + 5287615 * 2 ^ 59
def prefixEnd_5287615 : Nat := 4983230072969 + 3 ^ 40 * 5287615 * 2
def baseEnd_5287615 : Nat := 2715088010923434915695207

theorem tailTrace_5287615 : CollatzResearch.WordTrace tailWord_5287615 prefixEnd_5287615 2715088010923434915695207 := by
  unfold tailWord_5287615
  simp only [CollatzResearch.WordTrace]
  refine ⟨192855162738881382591408299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128570108492587588394272199 192855162738881382591408299)
  ·
    refine ⟨289282744108322073887112449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192855162738881382591408299 289282744108322073887112449)
    ·
      refine ⟨216962058081241555415334337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 289282744108322073887112449 216962058081241555415334337)
      ·
        refine ⟨162721543560931166561500753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 216962058081241555415334337 162721543560931166561500753)
        ·
          refine ⟨122041157670698374921125565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 162721543560931166561500753 122041157670698374921125565)
          ·
            refine ⟨45765434126511890595422087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 122041157670698374921125565 45765434126511890595422087)
            ·
              refine ⟨68648151189767835893133131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45765434126511890595422087 68648151189767835893133131)
              ·
                refine ⟨102972226784651753839699697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68648151189767835893133131 102972226784651753839699697)
                ·
                  refine ⟨77229170088488815379774773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 102972226784651753839699697 77229170088488815379774773)
                  ·
                    refine ⟨7240234695795826441853885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 77229170088488815379774773 7240234695795826441853885)
                    ·
                      refine ⟨2715088010923434915695207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7240234695795826441853885 2715088010923434915695207)
                      ·
                        rfl

theorem cell23_5287615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 1, 2, 5, 3].length) (baseStart_5287615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5287615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5287615 prefixEnd_5287615 := by exact prefixLift 5287615
  have htrace : WordTrace (prefixWord ++ tailWord_5287615) baseStart_5287615 baseEnd_5287615 := by
    simpa [prefixWord, tailWord_5287615, baseEnd_5287615] using wordTrace_append hprefix tailTrace_5287615
  have hstable : (prefixWord ++ tailWord_5287615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5287615).length < 2 ^ (prefixWord ++ tailWord_5287615).sum := by decide
  have hdescent : baseEnd_5287615 < baseStart_5287615 := by decide
  rcases family_descends (prefixWord ++ tailWord_5287615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5287672 : List Nat := [2, 1, 2, 1, 1, 2, 2, 6, 1, 1, 4]
def baseStart_5287672 : Nat := 118140960795 + 5287672 * 2 ^ 59
def prefixEnd_5287672 : Nat := 4983230072969 + 3 ^ 40 * 5287672 * 2
def baseEnd_5287672 : Nat := 2715117279320741192682445

theorem tailTrace_5287672 : CollatzResearch.WordTrace tailWord_5287672 prefixEnd_5287672 2715117279320741192682445 := by
  unfold tailWord_5287672
  simp only [CollatzResearch.WordTrace]
  refine ⟨96428620849837440663116635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128571494466449920884155513 96428620849837440663116635)
  ·
    refine ⟨144642931274756160994674953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96428620849837440663116635 144642931274756160994674953)
    ·
      refine ⟨108482198456067120746006215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144642931274756160994674953 108482198456067120746006215)
      ·
        refine ⟨162723297684100681119009323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108482198456067120746006215 162723297684100681119009323)
        ·
          refine ⟨244084946526151021678513985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162723297684100681119009323 244084946526151021678513985)
          ·
            refine ⟨183063709894613266258885489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 244084946526151021678513985 183063709894613266258885489)
            ·
              refine ⟨137297782420959949694164117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 183063709894613266258885489 137297782420959949694164117)
              ·
                refine ⟨6435833550982497641913943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 137297782420959949694164117 6435833550982497641913943)
                ·
                  refine ⟨9653750326473746462870915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6435833550982497641913943 9653750326473746462870915)
                  ·
                    refine ⟨14480625489710619694306373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9653750326473746462870915 14480625489710619694306373)
                    ·
                      refine ⟨2715117279320741192682445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14480625489710619694306373 2715117279320741192682445)
                      ·
                        rfl

theorem cell23_5287672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 6, 1, 1, 4].length) (baseStart_5287672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5287672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5287672 prefixEnd_5287672 := by exact prefixLift 5287672
  have htrace : WordTrace (prefixWord ++ tailWord_5287672) baseStart_5287672 baseEnd_5287672 := by
    simpa [prefixWord, tailWord_5287672, baseEnd_5287672] using wordTrace_append hprefix tailTrace_5287672
  have hstable : (prefixWord ++ tailWord_5287672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5287672).length < 2 ^ (prefixWord ++ tailWord_5287672).sum := by decide
  have hdescent : baseEnd_5287672 < baseStart_5287672 := by decide
  rcases family_descends (prefixWord ++ tailWord_5287672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5287692 : List Nat := [2, 2, 1, 2, 2, 1, 5, 1, 1, 1, 5]
def baseStart_5287692 : Nat := 118140960795 + 5287692 * 2 ^ 59
def prefixEnd_5287692 : Nat := 4983230072969 + 3 ^ 40 * 5287692 * 2
def baseEnd_5287692 : Nat := 2715127548933831114432353

theorem tailTrace_5287692 : CollatzResearch.WordTrace tailWord_5287692 prefixEnd_5287692 2715127548933831114432353 := by
  unfold tailWord_5287692
  simp only [CollatzResearch.WordTrace]
  refine ⟨96428985579801212370980665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128571980773068283161307553 96428985579801212370980665)
  ·
    refine ⟨72321739184850909278235499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96428985579801212370980665 72321739184850909278235499)
    ·
      refine ⟨108482608777276363917353249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72321739184850909278235499 108482608777276363917353249)
      ·
        refine ⟨81361956582957272938014937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108482608777276363917353249 81361956582957272938014937)
        ·
          refine ⟨61021467437217954703511203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81361956582957272938014937 61021467437217954703511203)
          ·
            refine ⟨91532201155826932055266805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61021467437217954703511203 91532201155826932055266805)
            ·
              refine ⟨8581143858358774880181263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 91532201155826932055266805 8581143858358774880181263)
              ·
                refine ⟨12871715787538162320271895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8581143858358774880181263 12871715787538162320271895)
                ·
                  refine ⟨19307573681307243480407843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12871715787538162320271895 19307573681307243480407843)
                  ·
                    refine ⟨28961360521960865220611765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19307573681307243480407843 28961360521960865220611765)
                    ·
                      refine ⟨2715127548933831114432353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28961360521960865220611765 2715127548933831114432353)
                      ·
                        rfl

theorem cell23_5287692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 5, 1, 1, 1, 5].length) (baseStart_5287692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5287692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5287692 prefixEnd_5287692 := by exact prefixLift 5287692
  have htrace : WordTrace (prefixWord ++ tailWord_5287692) baseStart_5287692 baseEnd_5287692 := by
    simpa [prefixWord, tailWord_5287692, baseEnd_5287692] using wordTrace_append hprefix tailTrace_5287692
  have hstable : (prefixWord ++ tailWord_5287692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5287692).length < 2 ^ (prefixWord ++ tailWord_5287692).sum := by decide
  have hdescent : baseEnd_5287692 < baseStart_5287692 := by decide
  rcases family_descends (prefixWord ++ tailWord_5287692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5287715 : List Nat := [1, 1, 1, 4, 2, 1, 2, 1, 2, 2, 6]
def baseStart_5287715 : Nat := 118140960795 + 5287715 * 2 ^ 59
def prefixEnd_5287715 : Nat := 4983230072969 + 3 ^ 40 * 5287715 * 2
def baseEnd_5287715 : Nat := 2715139358988884524444747

theorem tailTrace_5287715 : CollatzResearch.WordTrace tailWord_5287715 prefixEnd_5287715 2715139358988884524444747 := by
  unfold tailWord_5287715
  simp only [CollatzResearch.WordTrace]
  refine ⟨192858810038519099670048599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128572540025679399780032399 192858810038519099670048599)
  ·
    refine ⟨289288215057778649505072899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192858810038519099670048599 289288215057778649505072899)
    ·
      refine ⟨433932322586667974257609349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 289288215057778649505072899 433932322586667974257609349)
      ·
        refine ⟨81362310485000245173301753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 433932322586667974257609349 81362310485000245173301753)
        ·
          refine ⟨61021732863750183879976315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81362310485000245173301753 61021732863750183879976315)
          ·
            refine ⟨91532599295625275819964473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61021732863750183879976315 91532599295625275819964473)
            ·
              refine ⟨68649449471718956864973355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91532599295625275819964473 68649449471718956864973355)
              ·
                refine ⟨102974174207578435297460033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68649449471718956864973355 102974174207578435297460033)
                ·
                  refine ⟨77230630655683826473095025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 102974174207578435297460033 77230630655683826473095025)
                  ·
                    refine ⟨57922972991762869854821269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 77230630655683826473095025 57922972991762869854821269)
                    ·
                      refine ⟨2715139358988884524444747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 57922972991762869854821269 2715139358988884524444747)
                      ·
                        rfl

theorem cell23_5287715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 1, 2, 2, 6].length) (baseStart_5287715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5287715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5287715 prefixEnd_5287715 := by exact prefixLift 5287715
  have htrace : WordTrace (prefixWord ++ tailWord_5287715) baseStart_5287715 baseEnd_5287715 := by
    simpa [prefixWord, tailWord_5287715, baseEnd_5287715] using wordTrace_append hprefix tailTrace_5287715
  have hstable : (prefixWord ++ tailWord_5287715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5287715).length < 2 ^ (prefixWord ++ tailWord_5287715).sum := by decide
  have hdescent : baseEnd_5287715 < baseStart_5287715 := by decide
  rcases family_descends (prefixWord ++ tailWord_5287715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5287743 : List Nat := [1, 1, 2, 2, 6, 2, 2, 1, 1, 2, 3]
def baseStart_5287743 : Nat := 118140960795 + 5287743 * 2 ^ 59
def prefixEnd_5287743 : Nat := 4983230072969 + 3 ^ 40 * 5287743 * 2
def baseEnd_5287743 : Nat := 2715153736447210414894619

theorem tailTrace_5287743 : CollatzResearch.WordTrace tailWord_5287743 prefixEnd_5287743 2715153736447210414894619 := by
  unfold tailWord_5287743
  simp only [CollatzResearch.WordTrace]
  refine ⟨192859831282417660452067883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128573220854945106968045255 192859831282417660452067883)
  ·
    refine ⟨289289746923626490678101825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192859831282417660452067883 289289746923626490678101825)
    ·
      refine ⟨216967310192719868008576369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 289289746923626490678101825 216967310192719868008576369)
      ·
        refine ⟨162725482644539901006432277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 216967310192719868008576369 162725482644539901006432277)
        ·
          refine ⟨7627756998962807859676513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 162725482644539901006432277 7627756998962807859676513)
          ·
            refine ⟨5720817749222105894757385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7627756998962807859676513 5720817749222105894757385)
            ·
              refine ⟨4290613311916579421068039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5720817749222105894757385 4290613311916579421068039)
              ·
                refine ⟨6435919967874869131602059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4290613311916579421068039 6435919967874869131602059)
                ·
                  refine ⟨9653879951812303697403089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6435919967874869131602059 9653879951812303697403089)
                  ·
                    refine ⟨7240409963859227773052317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9653879951812303697403089 7240409963859227773052317)
                    ·
                      refine ⟨2715153736447210414894619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7240409963859227773052317 2715153736447210414894619)
                      ·
                        rfl

theorem cell23_5287743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 2, 1, 1, 2, 3].length) (baseStart_5287743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5287743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5287743 prefixEnd_5287743 := by exact prefixLift 5287743
  have htrace : WordTrace (prefixWord ++ tailWord_5287743) baseStart_5287743 baseEnd_5287743 := by
    simpa [prefixWord, tailWord_5287743, baseEnd_5287743] using wordTrace_append hprefix tailTrace_5287743
  have hstable : (prefixWord ++ tailWord_5287743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5287743).length < 2 ^ (prefixWord ++ tailWord_5287743).sum := by decide
  have hdescent : baseEnd_5287743 < baseStart_5287743 := by decide
  rcases family_descends (prefixWord ++ tailWord_5287743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5287750 : List Nat := [6, 1, 1, 2, 1, 3, 1, 2, 2, 4]
def baseStart_5287750 : Nat := 118140960795 + 5287750 * 2 ^ 59
def prefixEnd_5287750 : Nat := 4983230072969 + 3 ^ 40 * 5287750 * 2
def baseEnd_5287750 : Nat := 905052443603930629169029

theorem tailTrace_5287750 : CollatzResearch.WordTrace tailWord_5287750 prefixEnd_5287750 905052443603930629169029 := by
  unfold tailWord_5287750
  simp only [CollatzResearch.WordTrace]
  refine ⟨6026877706043509395236647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 128573391062261533765048469 6026877706043509395236647)
  ·
    refine ⟨9040316559065264092854971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6026877706043509395236647 9040316559065264092854971)
    ·
      refine ⟨13560474838597896139282457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9040316559065264092854971 13560474838597896139282457)
      ·
        refine ⟨10170356128948422104461843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13560474838597896139282457 10170356128948422104461843)
        ·
          refine ⟨15255534193422633156692765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10170356128948422104461843 15255534193422633156692765)
          ·
            refine ⟨5720825322533487433759787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15255534193422633156692765 5720825322533487433759787)
            ·
              refine ⟨8581237983800231150639681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5720825322533487433759787 8581237983800231150639681)
              ·
                refine ⟨6435928487850173362979761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8581237983800231150639681 6435928487850173362979761)
                ·
                  refine ⟨4826946365887630022234821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6435928487850173362979761 4826946365887630022234821)
                  ·
                    refine ⟨905052443603930629169029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4826946365887630022234821 905052443603930629169029)
                    ·
                      rfl

theorem cell23_5287750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 1, 2, 2, 4].length) (baseStart_5287750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5287750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5287750 prefixEnd_5287750 := by exact prefixLift 5287750
  have htrace : WordTrace (prefixWord ++ tailWord_5287750) baseStart_5287750 baseEnd_5287750 := by
    simpa [prefixWord, tailWord_5287750, baseEnd_5287750] using wordTrace_append hprefix tailTrace_5287750
  have hstable : (prefixWord ++ tailWord_5287750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5287750).length < 2 ^ (prefixWord ++ tailWord_5287750).sum := by decide
  have hdescent : baseEnd_5287750 < baseStart_5287750 := by decide
  rcases family_descends (prefixWord ++ tailWord_5287750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5287756 : List Nat := [2, 2, 1, 3, 4, 1, 1, 1, 4, 1, 3]
def baseStart_5287756 : Nat := 118140960795 + 5287756 * 2 ^ 59
def prefixEnd_5287756 : Nat := 4983230072969 + 3 ^ 40 * 5287756 * 2
def baseEnd_5287756 : Nat := 2715160411695718864032059

theorem tailTrace_5287756 : CollatzResearch.WordTrace tailWord_5287756 prefixEnd_5287756 2715160411695718864032059 := by
  unfold tailWord_5287756
  simp only [CollatzResearch.WordTrace]
  refine ⟨96430152715685281836145561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128573536954247042448194081 96430152715685281836145561)
  ·
    refine ⟨72322614536763961377109171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96430152715685281836145561 72322614536763961377109171)
    ·
      refine ⟨108483921805145942065663757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72322614536763961377109171 108483921805145942065663757)
      ·
        refine ⟨40681470676929728274623909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 108483921805145942065663757 40681470676929728274623909)
        ·
          refine ⟨7627775751924324051491983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40681470676929728274623909 7627775751924324051491983)
          ·
            refine ⟨11441663627886486077237975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7627775751924324051491983 11441663627886486077237975)
            ·
              refine ⟨17162495441829729115856963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11441663627886486077237975 17162495441829729115856963)
              ·
                refine ⟨25743743162744593673785445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17162495441829729115856963 25743743162744593673785445)
                ·
                  refine ⟨4826951843014611313834771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25743743162744593673785445 4826951843014611313834771)
                  ·
                    refine ⟨7240427764521916970752157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4826951843014611313834771 7240427764521916970752157)
                    ·
                      refine ⟨2715160411695718864032059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7240427764521916970752157 2715160411695718864032059)
                      ·
                        rfl

theorem cell23_5287756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 1, 1, 4, 1, 3].length) (baseStart_5287756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5287756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5287756 prefixEnd_5287756 := by exact prefixLift 5287756
  have htrace : WordTrace (prefixWord ++ tailWord_5287756) baseStart_5287756 baseEnd_5287756 := by
    simpa [prefixWord, tailWord_5287756, baseEnd_5287756] using wordTrace_append hprefix tailTrace_5287756
  have hstable : (prefixWord ++ tailWord_5287756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5287756).length < 2 ^ (prefixWord ++ tailWord_5287756).sum := by decide
  have hdescent : baseEnd_5287756 < baseStart_5287756 := by decide
  rcases family_descends (prefixWord ++ tailWord_5287756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5287872 : List Nat := [2, 1, 1, 2, 3, 2, 1, 1, 2, 3, 5]
def baseStart_5287872 : Nat := 118140960795 + 5287872 * 2 ^ 59
def prefixEnd_5287872 : Nat := 4983230072969 + 3 ^ 40 * 5287872 * 2
def baseEnd_5287872 : Nat := 2715219975451640410181525

theorem tailTrace_5287872 : CollatzResearch.WordTrace tailWord_5287872 prefixEnd_5287872 2715219975451640410181525 := by
  unfold tailWord_5287872
  simp only [CollatzResearch.WordTrace]
  refine ⟨96432268149475157741756935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128576357532633543655675913 96432268149475157741756935)
  ·
    refine ⟨144648402224212736612635403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96432268149475157741756935 144648402224212736612635403)
    ·
      refine ⟨216972603336319104918953105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144648402224212736612635403 216972603336319104918953105)
      ·
        refine ⟨162729452502239328689214829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 216972603336319104918953105 162729452502239328689214829)
        ·
          refine ⟨61023544688339748258455561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 162729452502239328689214829 61023544688339748258455561)
          ·
            refine ⟨45767658516254811193841671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61023544688339748258455561 45767658516254811193841671)
            ·
              refine ⟨68651487774382216790762507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45767658516254811193841671 68651487774382216790762507)
              ·
                refine ⟨102977231661573325186143761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68651487774382216790762507 102977231661573325186143761)
                ·
                  refine ⟨77232923746179993889607821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 102977231661573325186143761 77232923746179993889607821)
                  ·
                    refine ⟨28962346404817497708602933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 77232923746179993889607821 28962346404817497708602933)
                    ·
                      refine ⟨2715219975451640410181525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28962346404817497708602933 2715219975451640410181525)
                      ·
                        rfl

theorem cell23_5287872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 1, 2, 3, 5].length) (baseStart_5287872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5287872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5287872 prefixEnd_5287872 := by exact prefixLift 5287872
  have htrace : WordTrace (prefixWord ++ tailWord_5287872) baseStart_5287872 baseEnd_5287872 := by
    simpa [prefixWord, tailWord_5287872, baseEnd_5287872] using wordTrace_append hprefix tailTrace_5287872
  have hstable : (prefixWord ++ tailWord_5287872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5287872).length < 2 ^ (prefixWord ++ tailWord_5287872).sum := by decide
  have hdescent : baseEnd_5287872 < baseStart_5287872 := by decide
  rcases family_descends (prefixWord ++ tailWord_5287872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5287879 : List Nat := [1, 1, 4, 1, 1, 2, 1, 5, 3, 4]
def baseStart_5287879 : Nat := 118140960795 + 5287879 * 2 ^ 59
def prefixEnd_5287879 : Nat := 4983230072969 + 3 ^ 40 * 5287879 * 2
def baseEnd_5287879 : Nat := 905074523272073960931331

theorem tailTrace_5287879 : CollatzResearch.WordTrace tailWord_5287879 prefixEnd_5287879 905074523272073960931331 := by
  unfold tailWord_5287879
  simp only [CollatzResearch.WordTrace]
  refine ⟨192864791609924955679018691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128576527739949970452679127 192864791609924955679018691)
  ·
    refine ⟨289297187414887433518528037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192864791609924955679018691 289297187414887433518528037)
    ·
      refine ⟨54243222640291393784724007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 289297187414887433518528037 54243222640291393784724007)
      ·
        refine ⟨81364833960437090677086011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54243222640291393784724007 81364833960437090677086011)
        ·
          refine ⟨122047250940655636015629017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81364833960437090677086011 122047250940655636015629017)
          ·
            refine ⟨91535438205491727011721763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 122047250940655636015629017 91535438205491727011721763)
            ·
              refine ⟨137303157308237590517582645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91535438205491727011721763 137303157308237590517582645)
              ·
                refine ⟨12872170997647274111023373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 137303157308237590517582645 12872170997647274111023373)
                ·
                  refine ⟨4827064124117727791633765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12872170997647274111023373 4827064124117727791633765)
                  ·
                    refine ⟨905074523272073960931331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4827064124117727791633765 905074523272073960931331)
                    ·
                      rfl

theorem cell23_5287879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 5, 3, 4].length) (baseStart_5287879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5287879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5287879 prefixEnd_5287879 := by exact prefixLift 5287879
  have htrace : WordTrace (prefixWord ++ tailWord_5287879) baseStart_5287879 baseEnd_5287879 := by
    simpa [prefixWord, tailWord_5287879, baseEnd_5287879] using wordTrace_append hprefix tailTrace_5287879
  have hstable : (prefixWord ++ tailWord_5287879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5287879).length < 2 ^ (prefixWord ++ tailWord_5287879).sum := by decide
  have hdescent : baseEnd_5287879 < baseStart_5287879 := by decide
  rcases family_descends (prefixWord ++ tailWord_5287879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5287886 : List Nat := [4, 1, 1, 1, 2, 2, 3, 1, 2, 4, 2]
def baseStart_5287886 : Nat := 118140960795 + 5287886 * 2 ^ 59
def prefixEnd_5287886 : Nat := 4983230072969 + 3 ^ 40 * 5287886 * 2
def baseEnd_5287886 : Nat := 2715227164180803355406461

theorem tailTrace_5287886 : CollatzResearch.WordTrace tailWord_5287886 prefixEnd_5287886 2715227164180803355406461 := by
  unfold tailWord_5287886
  simp only [CollatzResearch.WordTrace]
  refine ⟨24108130865112449484315439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 128576697947266397249682341 24108130865112449484315439)
  ·
    refine ⟨36162196297668674226473159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24108130865112449484315439 36162196297668674226473159)
    ·
      refine ⟨54243294446503011339709739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36162196297668674226473159 54243294446503011339709739)
      ·
        refine ⟨81364941669754517009564609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54243294446503011339709739 81364941669754517009564609)
        ·
          refine ⟨61023706252315887757173457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81364941669754517009564609 61023706252315887757173457)
          ·
            refine ⟨45767779689236915817880093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61023706252315887757173457 45767779689236915817880093)
            ·
              refine ⟨17162917383463843431705035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45767779689236915817880093 17162917383463843431705035)
              ·
                refine ⟨25744376075195765147557553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17162917383463843431705035 25744376075195765147557553)
                ·
                  refine ⟨19308282056396823860668165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25744376075195765147557553 19308282056396823860668165)
                  ·
                    refine ⟨3620302885574404473875281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19308282056396823860668165 3620302885574404473875281)
                    ·
                      refine ⟨2715227164180803355406461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3620302885574404473875281 2715227164180803355406461)
                      ·
                        rfl

theorem cell23_5287886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 3, 1, 2, 4, 2].length) (baseStart_5287886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5287886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5287886 prefixEnd_5287886 := by exact prefixLift 5287886
  have htrace : WordTrace (prefixWord ++ tailWord_5287886) baseStart_5287886 baseEnd_5287886 := by
    simpa [prefixWord, tailWord_5287886, baseEnd_5287886] using wordTrace_append hprefix tailTrace_5287886
  have hstable : (prefixWord ++ tailWord_5287886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5287886).length < 2 ^ (prefixWord ++ tailWord_5287886).sum := by decide
  have hdescent : baseEnd_5287886 < baseStart_5287886 := by decide
  rcases family_descends (prefixWord ++ tailWord_5287886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5287926 : List Nat := [5, 1, 1, 1, 4, 1, 1, 1, 8]
def baseStart_5287926 : Nat := 118140960795 + 5287926 * 2 ^ 59
def prefixEnd_5287926 : Nat := 4983230072969 + 3 ^ 40 * 5287926 * 2
def baseEnd_5287926 : Nat := 301694189267442577656253

theorem tailTrace_5287926 : CollatzResearch.WordTrace tailWord_5287926 prefixEnd_5287926 301694189267442577656253 := by
  unfold tailWord_5287926
  simp only [CollatzResearch.WordTrace]
  refine ⟨12054156615047167669123727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 128577670560503121803986421 12054156615047167669123727)
  ·
    refine ⟨18081234922570751503685591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12054156615047167669123727 18081234922570751503685591)
    ·
      refine ⟨27121852383856127255528387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18081234922570751503685591 27121852383856127255528387)
      ·
        refine ⟨40682778575784190883292581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27121852383856127255528387 40682778575784190883292581)
        ·
          refine ⟨7628020982959535790617359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40682778575784190883292581 7628020982959535790617359)
          ·
            refine ⟨11442031474439303685926039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7628020982959535790617359 11442031474439303685926039)
            ·
              refine ⟨17163047211658955528889059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11442031474439303685926039 17163047211658955528889059)
              ·
                refine ⟨25744570817488433293333589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17163047211658955528889059 25744570817488433293333589)
                ·
                  refine ⟨301694189267442577656253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25744570817488433293333589 301694189267442577656253)
                  ·
                    rfl

theorem cell23_5287926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 1, 1, 8].length) (baseStart_5287926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5287926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5287926 prefixEnd_5287926 := by exact prefixLift 5287926
  have htrace : WordTrace (prefixWord ++ tailWord_5287926) baseStart_5287926 baseEnd_5287926 := by
    simpa [prefixWord, tailWord_5287926, baseEnd_5287926] using wordTrace_append hprefix tailTrace_5287926
  have hstable : (prefixWord ++ tailWord_5287926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5287926).length < 2 ^ (prefixWord ++ tailWord_5287926).sum := by decide
  have hdescent : baseEnd_5287926 < baseStart_5287926 := by decide
  rcases family_descends (prefixWord ++ tailWord_5287926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5287986 : List Nat := [3, 2, 1, 1, 2, 3, 2, 1, 4, 4]
def baseStart_5287986 : Nat := 118140960795 + 5287986 * 2 ^ 59
def prefixEnd_5287986 : Nat := 4983230072969 + 3 ^ 40 * 5287986 * 2
def baseEnd_5287986 : Nat := 905092837415417654718667

theorem tailTrace_5287986 : CollatzResearch.WordTrace tailWord_5287986 prefixEnd_5287986 905092837415417654718667 := by
  unfold tailWord_5287986
  simp only [CollatzResearch.WordTrace]
  refine ⟨48217173555134328238290953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128579129480358208635442541 48217173555134328238290953)
  ·
    refine ⟨36162880166350746178718215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48217173555134328238290953 36162880166350746178718215)
    ·
      refine ⟨54244320249526119268077323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36162880166350746178718215 54244320249526119268077323)
      ·
        refine ⟨81366480374289178902115985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54244320249526119268077323 81366480374289178902115985)
        ·
          refine ⟨61024860280716884176586989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81366480374289178902115985 61024860280716884176586989)
          ·
            refine ⟨22884322605268831566220121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61024860280716884176586989 22884322605268831566220121)
            ·
              refine ⟨17163241953951623674665091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22884322605268831566220121 17163241953951623674665091)
              ·
                refine ⟨25744862930927435511997637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17163241953951623674665091 25744862930927435511997637)
                ·
                  refine ⟨4827161799548894158499557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25744862930927435511997637 4827161799548894158499557)
                  ·
                    refine ⟨905092837415417654718667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4827161799548894158499557 905092837415417654718667)
                    ·
                      rfl

theorem cell23_5287986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 2, 1, 4, 4].length) (baseStart_5287986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5287986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5287986 prefixEnd_5287986 := by exact prefixLift 5287986
  have htrace : WordTrace (prefixWord ++ tailWord_5287986) baseStart_5287986 baseEnd_5287986 := by
    simpa [prefixWord, tailWord_5287986, baseEnd_5287986] using wordTrace_append hprefix tailTrace_5287986
  have hstable : (prefixWord ++ tailWord_5287986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5287986).length < 2 ^ (prefixWord ++ tailWord_5287986).sum := by decide
  have hdescent : baseEnd_5287986 < baseStart_5287986 := by decide
  rcases family_descends (prefixWord ++ tailWord_5287986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5287989 : List Nat := [1, 3, 3, 1, 1, 1, 3, 2, 1, 1, 6]
def baseStart_5287989 : Nat := 118140960795 + 5287989 * 2 ^ 59
def prefixEnd_5287989 : Nat := 4983230072969 + 3 ^ 40 * 5287989 * 2
def baseEnd_5287989 : Nat := 2715280052688216452418487

theorem tailTrace_5287989 : CollatzResearch.WordTrace tailWord_5287989 prefixEnd_5287989 2715280052688216452418487 := by
  unfold tailWord_5287989
  simp only [CollatzResearch.WordTrace]
  refine ⟨192868803639526444465523021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128579202426350962977015347 192868803639526444465523021)
  ·
    refine ⟨72325801364822416674571133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 192868803639526444465523021 72325801364822416674571133)
    ·
      refine ⟨27122175511808406252964175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72325801364822416674571133 27122175511808406252964175)
      ·
        refine ⟨40683263267712609379446263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27122175511808406252964175 40683263267712609379446263)
        ·
          refine ⟨61024894901568914069169395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40683263267712609379446263 61024894901568914069169395)
          ·
            refine ⟨91537342352353371103754093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61024894901568914069169395 91537342352353371103754093)
            ·
              refine ⟨34326503382132514163907785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 91537342352353371103754093 34326503382132514163907785)
              ·
                refine ⟨25744877536599385622930839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34326503382132514163907785 25744877536599385622930839)
                ·
                  refine ⟨38617316304899078434396259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25744877536599385622930839 38617316304899078434396259)
                  ·
                    refine ⟨57925974457348617651594389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 38617316304899078434396259 57925974457348617651594389)
                    ·
                      refine ⟨2715280052688216452418487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 57925974457348617651594389 2715280052688216452418487)
                      ·
                        rfl

theorem cell23_5287989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 2, 1, 1, 6].length) (baseStart_5287989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5287989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5287989 prefixEnd_5287989 := by exact prefixLift 5287989
  have htrace : WordTrace (prefixWord ++ tailWord_5287989) baseStart_5287989 baseEnd_5287989 := by
    simpa [prefixWord, tailWord_5287989, baseEnd_5287989] using wordTrace_append hprefix tailTrace_5287989
  have hstable : (prefixWord ++ tailWord_5287989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5287989).length < 2 ^ (prefixWord ++ tailWord_5287989).sum := by decide
  have hdescent : baseEnd_5287989 < baseStart_5287989 := by decide
  rcases family_descends (prefixWord ++ tailWord_5287989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5287996 : List Nat := [2, 2, 2, 2, 2, 1, 2, 2, 3, 2, 3]
def baseStart_5287996 : Nat := 118140960795 + 5287996 * 2 ^ 59
def prefixEnd_5287996 : Nat := 4983230072969 + 3 ^ 40 * 5287996 * 2
def baseEnd_5287996 : Nat := 2715283647052797925030955

theorem tailTrace_5287996 : CollatzResearch.WordTrace tailWord_5287996 prefixEnd_5287996 2715283647052797925030955 := by
  unfold tailWord_5287996
  simp only [CollatzResearch.WordTrace]
  refine ⟨96434529475250542330513921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128579372633667389774018561 96434529475250542330513921)
  ·
    refine ⟨72325897106437906747885441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96434529475250542330513921 72325897106437906747885441)
    ·
      refine ⟨54244422829828430060914081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72325897106437906747885441 54244422829828430060914081)
      ·
        refine ⟨40683317122371322545685561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54244422829828430060914081 40683317122371322545685561)
        ·
          refine ⟨30512487841778491909264171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40683317122371322545685561 30512487841778491909264171)
          ·
            refine ⟨45768731762667737863896257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30512487841778491909264171 45768731762667737863896257)
            ·
              refine ⟨34326548822000803397922193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45768731762667737863896257 34326548822000803397922193)
              ·
                refine ⟨25744911616500602548441645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34326548822000803397922193 25744911616500602548441645)
                ·
                  refine ⟨9654341856187725955665617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25744911616500602548441645 9654341856187725955665617)
                  ·
                    refine ⟨7240756392140794466749213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9654341856187725955665617 7240756392140794466749213)
                    ·
                      refine ⟨2715283647052797925030955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7240756392140794466749213 2715283647052797925030955)
                      ·
                        rfl

theorem cell23_5287996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 2, 3, 2, 3].length) (baseStart_5287996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5287996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5287996 prefixEnd_5287996 := by exact prefixLift 5287996
  have htrace : WordTrace (prefixWord ++ tailWord_5287996) baseStart_5287996 baseEnd_5287996 := by
    simpa [prefixWord, tailWord_5287996, baseEnd_5287996] using wordTrace_append hprefix tailTrace_5287996
  have hstable : (prefixWord ++ tailWord_5287996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5287996).length < 2 ^ (prefixWord ++ tailWord_5287996).sum := by decide
  have hdescent : baseEnd_5287996 < baseStart_5287996 := by decide
  rcases family_descends (prefixWord ++ tailWord_5287996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5288013 : List Nat := [1, 6, 1, 1, 1, 1, 3, 1, 3, 2, 3]
def baseStart_5288013 : Nat := 118140960795 + 5288013 * 2 ^ 59
def prefixEnd_5288013 : Nat := 4983230072969 + 3 ^ 40 * 5288013 * 2
def baseEnd_5288013 : Nat := 2715292376223924358518377

theorem tailTrace_5288013 : CollatzResearch.WordTrace tailWord_5288013 prefixEnd_5288013 2715292376223924358518377 := by
  unfold tailWord_5288013
  simp only [CollatzResearch.WordTrace]
  refine ⟨192869678991439496564396693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128579785994292997709597795 192869678991439496564396693)
  ·
    refine ⟨9040766202723726401456095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 192869678991439496564396693 9040766202723726401456095)
    ·
      refine ⟨13561149304085589602184143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9040766202723726401456095 13561149304085589602184143)
      ·
        refine ⟨20341723956128384403276215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13561149304085589602184143 20341723956128384403276215)
        ·
          refine ⟨30512585934192576604914323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20341723956128384403276215 30512585934192576604914323)
          ·
            refine ⟨45768878901288864907371485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30512585934192576604914323 45768878901288864907371485)
            ·
              refine ⟨17163329587983324340264307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45768878901288864907371485 17163329587983324340264307)
              ·
                refine ⟨25744994381974986510396461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17163329587983324340264307 25744994381974986510396461)
                ·
                  refine ⟨9654372893240619941398673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25744994381974986510396461 9654372893240619941398673)
                  ·
                    refine ⟨7240779669930464956049005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9654372893240619941398673 7240779669930464956049005)
                    ·
                      refine ⟨2715292376223924358518377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7240779669930464956049005 2715292376223924358518377)
                      ·
                        rfl

theorem cell23_5288013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 3, 1, 3, 2, 3].length) (baseStart_5288013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5288013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5288013 prefixEnd_5288013 := by exact prefixLift 5288013
  have htrace : WordTrace (prefixWord ++ tailWord_5288013) baseStart_5288013 baseEnd_5288013 := by
    simpa [prefixWord, tailWord_5288013, baseEnd_5288013] using wordTrace_append hprefix tailTrace_5288013
  have hstable : (prefixWord ++ tailWord_5288013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5288013).length < 2 ^ (prefixWord ++ tailWord_5288013).sum := by decide
  have hdescent : baseEnd_5288013 < baseStart_5288013 := by decide
  rcases family_descends (prefixWord ++ tailWord_5288013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5288026 : List Nat := [3, 1, 1, 2, 1, 1, 5, 2, 1, 3, 3]
def baseStart_5288026 : Nat := 118140960795 + 5288026 * 2 ^ 59
def prefixEnd_5288026 : Nat := 4983230072969 + 3 ^ 40 * 5288026 * 2
def baseEnd_5288026 : Nat := 2715299051472432807655817

theorem tailTrace_5288026 : CollatzResearch.WordTrace tailWord_5288026 prefixEnd_5288026 2715299051472432807655817 := by
  unfold tailWord_5288026
  simp only [CollatzResearch.WordTrace]
  refine ⟨48217538285098099946154983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128580102093594933189746621 48217538285098099946154983)
  ·
    refine ⟨72326307427647149919232475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48217538285098099946154983 72326307427647149919232475)
    ·
      refine ⟨108489461141470724878848713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72326307427647149919232475 108489461141470724878848713)
      ·
        refine ⟨81367095856103043659136535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108489461141470724878848713 81367095856103043659136535)
        ·
          refine ⟨122050643784154565488704803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81367095856103043659136535 122050643784154565488704803)
          ·
            refine ⟨183075965676231848233057205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122050643784154565488704803 183075965676231848233057205)
            ·
              refine ⟨17163371782146735771849113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 183075965676231848233057205 17163371782146735771849113)
              ·
                refine ⟨12872528836610051828886835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17163371782146735771849113 12872528836610051828886835)
                ·
                  refine ⟨19308793254915077743330253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12872528836610051828886835 19308793254915077743330253)
                  ·
                    refine ⟨7240797470593154153748845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19308793254915077743330253 7240797470593154153748845)
                    ·
                      refine ⟨2715299051472432807655817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7240797470593154153748845 2715299051472432807655817)
                      ·
                        rfl

theorem cell23_5288026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 5, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 5, 2, 1, 3, 3].length) (baseStart_5288026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5288026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5288026 prefixEnd_5288026 := by exact prefixLift 5288026
  have htrace : WordTrace (prefixWord ++ tailWord_5288026) baseStart_5288026 baseEnd_5288026 := by
    simpa [prefixWord, tailWord_5288026, baseEnd_5288026] using wordTrace_append hprefix tailTrace_5288026
  have hstable : (prefixWord ++ tailWord_5288026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5288026).length < 2 ^ (prefixWord ++ tailWord_5288026).sum := by decide
  have hdescent : baseEnd_5288026 < baseStart_5288026 := by decide
  rcases family_descends (prefixWord ++ tailWord_5288026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5288044 : List Nat := [2, 2, 1, 1, 3, 5, 2, 2, 1, 2, 2]
def baseStart_5288044 : Nat := 118140960795 + 5288044 * 2 ^ 59
def prefixEnd_5288044 : Nat := 4983230072969 + 3 ^ 40 * 5288044 * 2
def baseEnd_5288044 : Nat := 2715308294124213737230735

theorem tailTrace_5288044 : CollatzResearch.WordTrace tailWord_5288044 prefixEnd_5288044 2715308294124213737230735 := by
  unfold tailWord_5288044
  simp only [CollatzResearch.WordTrace]
  refine ⟨96435404827163594429387593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128580539769551459239183457 96435404827163594429387593)
  ·
    refine ⟨72326553620372695822040695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96435404827163594429387593 72326553620372695822040695)
    ·
      refine ⟨108489830430559043733061043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72326553620372695822040695 108489830430559043733061043)
      ·
        refine ⟨162734745645838565599591565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108489830430559043733061043 162734745645838565599591565)
        ·
          refine ⟨61025529617189462099846837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 162734745645838565599591565 61025529617189462099846837)
          ·
            refine ⟨5721143401611512071860641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 61025529617189462099846837 5721143401611512071860641)
            ·
              refine ⟨4290857551208634053895481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5721143401611512071860641 4290857551208634053895481)
              ·
                refine ⟨3218143163406475540421611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4290857551208634053895481 3218143163406475540421611)
                ·
                  refine ⟨4827214745109713310632417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3218143163406475540421611 4827214745109713310632417)
                  ·
                    refine ⟨3620411058832284982974313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4827214745109713310632417 3620411058832284982974313)
                    ·
                      refine ⟨2715308294124213737230735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3620411058832284982974313 2715308294124213737230735)
                      ·
                        rfl

theorem cell23_5288044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 2, 2, 1, 2, 2].length) (baseStart_5288044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5288044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5288044 prefixEnd_5288044 := by exact prefixLift 5288044
  have htrace : WordTrace (prefixWord ++ tailWord_5288044) baseStart_5288044 baseEnd_5288044 := by
    simpa [prefixWord, tailWord_5288044, baseEnd_5288044] using wordTrace_append hprefix tailTrace_5288044
  have hstable : (prefixWord ++ tailWord_5288044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5288044).length < 2 ^ (prefixWord ++ tailWord_5288044).sum := by decide
  have hdescent : baseEnd_5288044 < baseStart_5288044 := by decide
  rcases family_descends (prefixWord ++ tailWord_5288044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5288049 : List Nat := [1, 2, 2, 2, 1, 1, 3, 1, 1, 5, 4]
def baseStart_5288049 : Nat := 118140960795 + 5288049 * 2 ^ 59
def prefixEnd_5288049 : Nat := 4983230072969 + 3 ^ 40 * 5288049 * 2
def baseEnd_5288049 : Nat := 2715310861527486217668211

theorem tailTrace_5288049 : CollatzResearch.WordTrace tailWord_5288049 prefixEnd_5288049 2715310861527486217668211 := by
  unfold tailWord_5288049
  simp only [CollatzResearch.WordTrace]
  refine ⟨192870992019309074712707201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128580661346206049808471467 192870992019309074712707201)
  ·
    refine ⟨144653244014481806034530401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192870992019309074712707201 144653244014481806034530401)
    ·
      refine ⟨108489933010861354525897801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144653244014481806034530401 108489933010861354525897801)
      ·
        refine ⟨81367449758146015894423351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108489933010861354525897801 81367449758146015894423351)
        ·
          refine ⟨122051174637219023841635027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81367449758146015894423351 122051174637219023841635027)
          ·
            refine ⟨183076761955828535762452541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122051174637219023841635027 183076761955828535762452541)
            ·
              refine ⟨68653785733435700910919703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 183076761955828535762452541 68653785733435700910919703)
              ·
                refine ⟨102980678600153551366379555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68653785733435700910919703 102980678600153551366379555)
                ·
                  refine ⟨154471017900230327049569333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 102980678600153551366379555 154471017900230327049569333)
                  ·
                    refine ⟨14481657928146593160897125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 154471017900230327049569333 14481657928146593160897125)
                    ·
                      refine ⟨2715310861527486217668211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14481657928146593160897125 2715310861527486217668211)
                      ·
                        rfl

theorem cell23_5288049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 1, 1, 5, 4].length) (baseStart_5288049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5288049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5288049 prefixEnd_5288049 := by exact prefixLift 5288049
  have htrace : WordTrace (prefixWord ++ tailWord_5288049) baseStart_5288049 baseEnd_5288049 := by
    simpa [prefixWord, tailWord_5288049, baseEnd_5288049] using wordTrace_append hprefix tailTrace_5288049
  have hstable : (prefixWord ++ tailWord_5288049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5288049).length < 2 ^ (prefixWord ++ tailWord_5288049).sum := by decide
  have hdescent : baseEnd_5288049 < baseStart_5288049 := by decide
  rcases family_descends (prefixWord ++ tailWord_5288049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5288083 : List Nat := [1, 1, 1, 2, 1, 2, 3, 4, 4, 2, 2]
def baseStart_5288083 : Nat := 118140960795 + 5288083 * 2 ^ 59
def prefixEnd_5288083 : Nat := 4983230072969 + 3 ^ 40 * 5288083 * 2
def baseEnd_5288083 : Nat := 2715328319869739084643055

theorem tailTrace_5288083 : CollatzResearch.WordTrace tailWord_5288083 prefixEnd_5288083 2715328319869739084643055 := by
  unfold tailWord_5288083
  simp only [CollatzResearch.WordTrace]
  refine ⟨192872232101185898519444903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128581488067457265679629935 192872232101185898519444903)
  ·
    refine ⟨289308348151778847779167355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192872232101185898519444903 289308348151778847779167355)
    ·
      refine ⟨433962522227668271668751033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 289308348151778847779167355 433962522227668271668751033)
      ·
        refine ⟨325471891670751203751563275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 433962522227668271668751033 325471891670751203751563275)
        ·
          refine ⟨488207837506126805627344913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 325471891670751203751563275 488207837506126805627344913)
          ·
            refine ⟨366155878129595104220508685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 488207837506126805627344913 366155878129595104220508685)
            ·
              refine ⟨137308454298598164082690757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 366155878129595104220508685 137308454298598164082690757)
              ·
                refine ⟨25745335180987155765504517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 137308454298598164082690757 25745335180987155765504517)
                ·
                  refine ⟨4827250346435091706032097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25745335180987155765504517 4827250346435091706032097)
                  ·
                    refine ⟨3620437759826318779524073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4827250346435091706032097 3620437759826318779524073)
                    ·
                      refine ⟨2715328319869739084643055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3620437759826318779524073 2715328319869739084643055)
                      ·
                        rfl

theorem cell23_5288083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 4, 4, 2, 2].length) (baseStart_5288083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5288083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5288083 prefixEnd_5288083 := by exact prefixLift 5288083
  have htrace : WordTrace (prefixWord ++ tailWord_5288083) baseStart_5288083 baseEnd_5288083 := by
    simpa [prefixWord, tailWord_5288083, baseEnd_5288083] using wordTrace_append hprefix tailTrace_5288083
  have hstable : (prefixWord ++ tailWord_5288083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5288083).length < 2 ^ (prefixWord ++ tailWord_5288083).sum := by decide
  have hdescent : baseEnd_5288083 < baseStart_5288083 := by decide
  rcases family_descends (prefixWord ++ tailWord_5288083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5288094 : List Nat := [4, 3, 1, 1, 3, 2, 1, 2, 2, 1, 3]
def baseStart_5288094 : Nat := 118140960795 + 5288094 * 2 ^ 59
def prefixEnd_5288094 : Nat := 4983230072969 + 3 ^ 40 * 5288094 * 2
def baseEnd_5288094 : Nat := 2715333968156938541605505

theorem tailTrace_5288094 : CollatzResearch.WordTrace tailWord_5288094 prefixEnd_5288094 2715333968156938541605505 := by
  unfold tailWord_5288094
  simp only [CollatzResearch.WordTrace]
  refine ⟨24109079163018255924761917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 128581755536097364932063557 24109079163018255924761917)
  ·
    refine ⟨9040904686131845971785719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24109079163018255924761917 9040904686131845971785719)
    ·
      refine ⟨13561357029197768957678579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9040904686131845971785719 13561357029197768957678579)
      ·
        refine ⟨20342035543796653436517869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13561357029197768957678579 20342035543796653436517869)
        ·
          refine ⟨7628263328923745038694201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20342035543796653436517869 7628263328923745038694201)
          ·
            refine ⟨5721197496692808779020651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7628263328923745038694201 5721197496692808779020651)
            ·
              refine ⟨8581796245039213168530977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5721197496692808779020651 8581796245039213168530977)
              ·
                refine ⟨6436347183779409876398233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8581796245039213168530977 6436347183779409876398233)
                ·
                  refine ⟨4827260387834557407298675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6436347183779409876398233 4827260387834557407298675)
                  ·
                    refine ⟨7240890581751836110948013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4827260387834557407298675 7240890581751836110948013)
                    ·
                      refine ⟨2715333968156938541605505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7240890581751836110948013 2715333968156938541605505)
                      ·
                        rfl

theorem cell23_5288094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 1, 2, 2, 1, 3].length) (baseStart_5288094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5288094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5288094 prefixEnd_5288094 := by exact prefixLift 5288094
  have htrace : WordTrace (prefixWord ++ tailWord_5288094) baseStart_5288094 baseEnd_5288094 := by
    simpa [prefixWord, tailWord_5288094, baseEnd_5288094] using wordTrace_append hprefix tailTrace_5288094
  have hstable : (prefixWord ++ tailWord_5288094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5288094).length < 2 ^ (prefixWord ++ tailWord_5288094).sum := by decide
  have hdescent : baseEnd_5288094 < baseStart_5288094 := by decide
  rcases family_descends (prefixWord ++ tailWord_5288094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5288096 : List Nat := [2, 1, 1, 4, 2, 2, 1, 2, 2, 2, 4]
def baseStart_5288096 : Nat := 118140960795 + 5288096 * 2 ^ 59
def prefixEnd_5288096 : Nat := 4983230072969 + 3 ^ 40 * 5288096 * 2
def baseEnd_5288096 : Nat := 2715334995118247533780495

theorem tailTrace_5288096 : CollatzResearch.WordTrace tailWord_5288096 prefixEnd_5288096 2715334995118247533780495 := by
  unfold tailWord_5288096
  simp only [CollatzResearch.WordTrace]
  refine ⟨96436353125069400869834071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128581804166759201159778761 96436353125069400869834071)
  ·
    refine ⟨144654529687604101304751107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96436353125069400869834071 144654529687604101304751107)
    ·
      refine ⟨216981794531406151957126661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144654529687604101304751107 216981794531406151957126661)
      ·
        refine ⟨40684086474638653491961249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 216981794531406151957126661 40684086474638653491961249)
        ·
          refine ⟨30513064855978990118970937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40684086474638653491961249 30513064855978990118970937)
          ·
            refine ⟨22884798641984242589228203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30513064855978990118970937 22884798641984242589228203)
            ·
              refine ⟨34327197962976363883842305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22884798641984242589228203 34327197962976363883842305)
              ·
                refine ⟨25745398472232272912881729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34327197962976363883842305 25745398472232272912881729)
                ·
                  refine ⟨19309048854174204684661297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25745398472232272912881729 19309048854174204684661297)
                  ·
                    refine ⟨14481786640630653513495973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19309048854174204684661297 14481786640630653513495973)
                    ·
                      refine ⟨2715334995118247533780495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14481786640630653513495973 2715334995118247533780495)
                      ·
                        rfl

theorem cell23_5288096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 2, 2, 2, 4].length) (baseStart_5288096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5288096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5288096 prefixEnd_5288096 := by exact prefixLift 5288096
  have htrace : WordTrace (prefixWord ++ tailWord_5288096) baseStart_5288096 baseEnd_5288096 := by
    simpa [prefixWord, tailWord_5288096, baseEnd_5288096] using wordTrace_append hprefix tailTrace_5288096
  have hstable : (prefixWord ++ tailWord_5288096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5288096).length < 2 ^ (prefixWord ++ tailWord_5288096).sum := by decide
  have hdescent : baseEnd_5288096 < baseStart_5288096 := by decide
  rcases family_descends (prefixWord ++ tailWord_5288096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5288136 : List Nat := [2, 1, 3, 1, 2, 1, 1, 5, 2, 5]
def baseStart_5288136 : Nat := 118140960795 + 5288136 * 2 ^ 59
def prefixEnd_5288136 : Nat := 4983230072969 + 3 ^ 40 * 5288136 * 2
def baseEnd_5288136 : Nat := 905118511448142459093437

theorem tailTrace_5288136 : CollatzResearch.WordTrace tailWord_5288136 prefixEnd_5288136 905118511448142459093437 := by
  unfold tailWord_5288136
  simp only [CollatzResearch.WordTrace]
  refine ⟨96437082584996944285562131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128582776779995925714082841 96437082584996944285562131)
  ·
    refine ⟨144655623877495416428343197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96437082584996944285562131 144655623877495416428343197)
    ·
      refine ⟨54245858954060781160628699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 144655623877495416428343197 54245858954060781160628699)
      ·
        refine ⟨81368788431091171740943049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54245858954060781160628699 81368788431091171740943049)
        ·
          refine ⟨61026591323318378805707287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81368788431091171740943049 61026591323318378805707287)
          ·
            refine ⟨91539886984977568208560931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61026591323318378805707287 91539886984977568208560931)
            ·
              refine ⟨137309830477466352312841397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91539886984977568208560931 137309830477466352312841397)
              ·
                refine ⟨12872796607262470529328881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 137309830477466352312841397 12872796607262470529328881)
                ·
                  refine ⟨9654597455446852896996661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12872796607262470529328881 9654597455446852896996661)
                  ·
                    refine ⟨905118511448142459093437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9654597455446852896996661 905118511448142459093437)
                    ·
                      rfl

theorem cell23_5288136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 5, 2, 5].length) (baseStart_5288136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5288136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5288136 prefixEnd_5288136 := by exact prefixLift 5288136
  have htrace : WordTrace (prefixWord ++ tailWord_5288136) baseStart_5288136 baseEnd_5288136 := by
    simpa [prefixWord, tailWord_5288136, baseEnd_5288136] using wordTrace_append hprefix tailTrace_5288136
  have hstable : (prefixWord ++ tailWord_5288136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5288136).length < 2 ^ (prefixWord ++ tailWord_5288136).sum := by decide
  have hdescent : baseEnd_5288136 < baseStart_5288136 := by decide
  rcases family_descends (prefixWord ++ tailWord_5288136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5288157 : List Nat := [1, 4, 3, 2, 1, 2, 3, 2, 5]
def baseStart_5288157 : Nat := 118140960795 + 5288157 * 2 ^ 59
def prefixEnd_5288157 : Nat := 4983230072969 + 3 ^ 40 * 5288157 * 2
def baseEnd_5288157 : Nat := 301707368604241310568635

theorem tailTrace_5288157 : CollatzResearch.WordTrace tailWord_5288157 prefixEnd_5288157 301707368604241310568635 := by
  unfold tailWord_5288157
  simp only [CollatzResearch.WordTrace]
  refine ⟨192874931102917809157638725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128583287401945206105092483 192874931102917809157638725)
  ·
    refine ⟨36164049581797089217057261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 192874931102917809157638725 36164049581797089217057261)
    ·
      refine ⟨13561518593173908456396473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36164049581797089217057261 13561518593173908456396473)
      ·
        refine ⟨10171138944880431342297355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13561518593173908456396473 10171138944880431342297355)
        ·
          refine ⟨15256708417320647013446033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10171138944880431342297355 15256708417320647013446033)
          ·
            refine ⟨11442531312990485260084525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15256708417320647013446033 11442531312990485260084525)
            ·
              refine ⟨4290949242371431972531697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11442531312990485260084525 4290949242371431972531697)
              ·
                refine ⟨3218211931778573979398773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4290949242371431972531697 3218211931778573979398773)
                ·
                  refine ⟨301707368604241310568635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3218211931778573979398773 301707368604241310568635)
                  ·
                    rfl

theorem cell23_5288157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 3, 2, 5].length) (baseStart_5288157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5288157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5288157 prefixEnd_5288157 := by exact prefixLift 5288157
  have htrace : WordTrace (prefixWord ++ tailWord_5288157) baseStart_5288157 baseEnd_5288157 := by
    simpa [prefixWord, tailWord_5288157, baseEnd_5288157] using wordTrace_append hprefix tailTrace_5288157
  have hstable : (prefixWord ++ tailWord_5288157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5288157).length < 2 ^ (prefixWord ++ tailWord_5288157).sum := by decide
  have hdescent : baseEnd_5288157 < baseStart_5288157 := by decide
  rcases family_descends (prefixWord ++ tailWord_5288157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5288176 : List Nat := [2, 1, 1, 1, 3, 1, 1, 3, 3, 4, 3]
def baseStart_5288176 : Nat := 118140960795 + 5288176 * 2 ^ 59
def prefixEnd_5288176 : Nat := 4983230072969 + 3 ^ 40 * 5288176 * 2
def baseEnd_5288176 : Nat := 2715376073570607220780127

theorem tailTrace_5288176 : CollatzResearch.WordTrace tailWord_5288176 prefixEnd_5288176 2715376073570607220780127 := by
  unfold tailWord_5288176
  simp only [CollatzResearch.WordTrace]
  refine ⟨96437812044924487701290191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128583749393232650268386921 96437812044924487701290191)
  ·
    refine ⟨144656718067386731551935287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96437812044924487701290191 144656718067386731551935287)
    ·
      refine ⟨216985077101080097327902931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144656718067386731551935287 216985077101080097327902931)
      ·
        refine ⟨325477615651620145991854397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 216985077101080097327902931 325477615651620145991854397)
        ·
          refine ⟨122054105869357554746945399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 325477615651620145991854397 122054105869357554746945399)
          ·
            refine ⟨183081158804036332120418099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122054105869357554746945399 183081158804036332120418099)
            ·
              refine ⟨274621738206054498180627149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 183081158804036332120418099 274621738206054498180627149)
              ·
                refine ⟨102983151827270436817735181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 274621738206054498180627149 102983151827270436817735181)
                ·
                  refine ⟨38618681935226413806650693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 102983151827270436817735181 38618681935226413806650693)
                  ·
                    refine ⟨7241002862854952588747005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 38618681935226413806650693 7241002862854952588747005)
                    ·
                      refine ⟨2715376073570607220780127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7241002862854952588747005 2715376073570607220780127)
                      ·
                        rfl

theorem cell23_5288176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 3, 3, 4, 3].length) (baseStart_5288176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5288176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5288176 prefixEnd_5288176 := by exact prefixLift 5288176
  have htrace : WordTrace (prefixWord ++ tailWord_5288176) baseStart_5288176 baseEnd_5288176 := by
    simpa [prefixWord, tailWord_5288176, baseEnd_5288176] using wordTrace_append hprefix tailTrace_5288176
  have hstable : (prefixWord ++ tailWord_5288176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5288176).length < 2 ^ (prefixWord ++ tailWord_5288176).sum := by decide
  have hdescent : baseEnd_5288176 < baseStart_5288176 := by decide
  rcases family_descends (prefixWord ++ tailWord_5288176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5288190 : List Nat := [4, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4]
def baseStart_5288190 : Nat := 118140960795 + 5288190 * 2 ^ 59
def prefixEnd_5288190 : Nat := 4983230072969 + 3 ^ 40 * 5288190 * 2
def baseEnd_5288190 : Nat := 2715383262299770166005063

theorem tailTrace_5288190 : CollatzResearch.WordTrace tailWord_5288190 prefixEnd_5288190 2715383262299770166005063 := by
  unfold tailWord_5288190
  simp only [CollatzResearch.WordTrace]
  refine ⟨24109516838974781974198753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 128584089807865503862393349 24109516838974781974198753)
  ·
    refine ⟨18082137629231086480649065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24109516838974781974198753 18082137629231086480649065)
    ·
      refine ⟨13561603221923314860486799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18082137629231086480649065 13561603221923314860486799)
      ·
        refine ⟨20342404832884972290730199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13561603221923314860486799 20342404832884972290730199)
        ·
          refine ⟨30513607249327458436095299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20342404832884972290730199 30513607249327458436095299)
          ·
            refine ⟨45770410873991187654142949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30513607249327458436095299 45770410873991187654142949)
            ·
              refine ⟨8581952038873347685151803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45770410873991187654142949 8581952038873347685151803)
              ·
                refine ⟨12872928058310021527727705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8581952038873347685151803 12872928058310021527727705)
                ·
                  refine ⟨9654696043732516145795779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12872928058310021527727705 9654696043732516145795779)
                  ·
                    refine ⟨14482044065598774218693669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9654696043732516145795779 14482044065598774218693669)
                    ·
                      refine ⟨2715383262299770166005063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14482044065598774218693669 2715383262299770166005063)
                      ·
                        rfl

theorem cell23_5288190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4].length) (baseStart_5288190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5288190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5288190 prefixEnd_5288190 := by exact prefixLift 5288190
  have htrace : WordTrace (prefixWord ++ tailWord_5288190) baseStart_5288190 baseEnd_5288190 := by
    simpa [prefixWord, tailWord_5288190, baseEnd_5288190] using wordTrace_append hprefix tailTrace_5288190
  have hstable : (prefixWord ++ tailWord_5288190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5288190).length < 2 ^ (prefixWord ++ tailWord_5288190).sum := by decide
  have hdescent : baseEnd_5288190 < baseStart_5288190 := by decide
  rcases family_descends (prefixWord ++ tailWord_5288190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5288216 : List Nat := [2, 1, 2, 3, 1, 2, 2, 1, 1, 2, 6]
def baseStart_5288216 : Nat := 118140960795 + 5288216 * 2 ^ 59
def prefixEnd_5288216 : Nat := 4983230072969 + 3 ^ 40 * 5288216 * 2
def baseEnd_5288216 : Nat := 2715396612796787064279943

theorem tailTrace_5288216 : CollatzResearch.WordTrace tailWord_5288216 prefixEnd_5288216 2715396612796787064279943 := by
  unfold tailWord_5288216
  simp only [CollatzResearch.WordTrace]
  refine ⟨96438541504852031117018251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128584722006469374822691001 96438541504852031117018251)
  ·
    refine ⟨144657812257278046675527377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96438541504852031117018251 144657812257278046675527377)
    ·
      refine ⟨108493359192958535006645533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144657812257278046675527377 108493359192958535006645533)
      ·
        refine ⟨40685009697359450627492075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 108493359192958535006645533 40685009697359450627492075)
        ·
          refine ⟨61027514546039175941238113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40685009697359450627492075 61027514546039175941238113)
          ·
            refine ⟨45770635909529381955928585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61027514546039175941238113 45770635909529381955928585)
            ·
              refine ⟨34327976932147036466946439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45770635909529381955928585 34327976932147036466946439)
              ·
                refine ⟨51491965398220554700419659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34327976932147036466946439 51491965398220554700419659)
                ·
                  refine ⟨77237948097330832050629489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51491965398220554700419659 77237948097330832050629489)
                  ·
                    refine ⟨57928461072998124037972117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 77237948097330832050629489 57928461072998124037972117)
                    ·
                      refine ⟨2715396612796787064279943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 57928461072998124037972117 2715396612796787064279943)
                      ·
                        rfl

theorem cell23_5288216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 1, 1, 2, 6].length) (baseStart_5288216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5288216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5288216 prefixEnd_5288216 := by exact prefixLift 5288216
  have htrace : WordTrace (prefixWord ++ tailWord_5288216) baseStart_5288216 baseEnd_5288216 := by
    simpa [prefixWord, tailWord_5288216, baseEnd_5288216] using wordTrace_append hprefix tailTrace_5288216
  have hstable : (prefixWord ++ tailWord_5288216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5288216).length < 2 ^ (prefixWord ++ tailWord_5288216).sum := by decide
  have hdescent : baseEnd_5288216 < baseStart_5288216 := by decide
  rcases family_descends (prefixWord ++ tailWord_5288216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5288243 : List Nat := [1, 1, 1, 2, 5, 1, 2, 4, 1, 5]
def baseStart_5288243 : Nat := 118140960795 + 5288243 * 2 ^ 59
def prefixEnd_5288243 : Nat := 4983230072969 + 3 ^ 40 * 5288243 * 2
def baseEnd_5288243 : Nat := 905136825591486152880773

theorem tailTrace_5288243 : CollatzResearch.WordTrace tailWord_5288243 prefixEnd_5288243 905136825591486152880773 := by
  unfold tailWord_5288243
  simp only [CollatzResearch.WordTrace]
  refine ⟨192878067780606245845269383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128585378520404163896846255 192878067780606245845269383)
  ·
    refine ⟨289317101670909368767904075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192878067780606245845269383 289317101670909368767904075)
    ·
      refine ⟨433975652506364053151856113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 289317101670909368767904075 433975652506364053151856113)
      ·
        refine ⟨325481739379773039863892085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 433975652506364053151856113 325481739379773039863892085)
        ·
          refine ⟨30513913066853722487239883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 325481739379773039863892085 30513913066853722487239883)
          ·
            refine ⟨45770869600280583730859825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30513913066853722487239883 45770869600280583730859825)
            ·
              refine ⟨34328152200210437798144869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45770869600280583730859825 34328152200210437798144869)
              ·
                refine ⟨6436528537539457087152163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34328152200210437798144869 6436528537539457087152163)
                ·
                  refine ⟨9654792806309185630728245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6436528537539457087152163 9654792806309185630728245)
                  ·
                    refine ⟨905136825591486152880773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9654792806309185630728245 905136825591486152880773)
                    ·
                      rfl

theorem cell23_5288243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 4, 1, 5].length) (baseStart_5288243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5288243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5288243 prefixEnd_5288243 := by exact prefixLift 5288243
  have htrace : WordTrace (prefixWord ++ tailWord_5288243) baseStart_5288243 baseEnd_5288243 := by
    simpa [prefixWord, tailWord_5288243, baseEnd_5288243] using wordTrace_append hprefix tailTrace_5288243
  have hstable : (prefixWord ++ tailWord_5288243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5288243).length < 2 ^ (prefixWord ++ tailWord_5288243).sum := by decide
  have hdescent : baseEnd_5288243 < baseStart_5288243 := by decide
  rcases family_descends (prefixWord ++ tailWord_5288243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5288250 : List Nat := [3, 1, 1, 1, 4, 3, 1, 1, 1, 5, 2]
def baseStart_5288250 : Nat := 118140960795 + 5288250 * 2 ^ 59
def prefixEnd_5288250 : Nat := 4983230072969 + 3 ^ 40 * 5288250 * 2
def baseEnd_5288250 : Nat := 2715414071139039931254787

theorem tailTrace_5288250 : CollatzResearch.WordTrace tailWord_5288250 prefixEnd_5288250 2715414071139039931254787 := by
  unfold tailWord_5288250
  simp only [CollatzResearch.WordTrace]
  refine ⟨48219580772895221510193551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128585548727720590693849469 48219580772895221510193551)
  ·
    refine ⟨72329371159342832265290327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48219580772895221510193551 72329371159342832265290327)
    ·
      refine ⟨108494056739014248397935491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72329371159342832265290327 108494056739014248397935491)
      ·
        refine ⟨162741085108521372596903237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108494056739014248397935491 162741085108521372596903237)
        ·
          refine ⟨30513953457847757361919357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 162741085108521372596903237 30513953457847757361919357)
          ·
            refine ⟨11442732546692909010719759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30513953457847757361919357 11442732546692909010719759)
            ·
              refine ⟨17164098820039363516079639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11442732546692909010719759 17164098820039363516079639)
              ·
                refine ⟨25746148230059045274119459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17164098820039363516079639 25746148230059045274119459)
                ·
                  refine ⟨38619222345088567911179189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25746148230059045274119459 38619222345088567911179189)
                  ·
                    refine ⟨3620552094852053241673049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 38619222345088567911179189 3620552094852053241673049)
                    ·
                      refine ⟨2715414071139039931254787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3620552094852053241673049 2715414071139039931254787)
                      ·
                        rfl

theorem cell23_5288250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 1, 1, 1, 5, 2].length) (baseStart_5288250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5288250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5288250 prefixEnd_5288250 := by exact prefixLift 5288250
  have htrace : WordTrace (prefixWord ++ tailWord_5288250) baseStart_5288250 baseEnd_5288250 := by
    simpa [prefixWord, tailWord_5288250, baseEnd_5288250] using wordTrace_append hprefix tailTrace_5288250
  have hstable : (prefixWord ++ tailWord_5288250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5288250).length < 2 ^ (prefixWord ++ tailWord_5288250).sum := by decide
  have hdescent : baseEnd_5288250 < baseStart_5288250 := by decide
  rcases family_descends (prefixWord ++ tailWord_5288250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5288256 : List Nat := [2, 1, 1, 2, 2, 1, 2, 3, 3, 6]
def baseStart_5288256 : Nat := 118140960795 + 5288256 * 2 ^ 59
def prefixEnd_5288256 : Nat := 4983230072969 + 3 ^ 40 * 5288256 * 2
def baseEnd_5288256 : Nat := 905139050674322302593253

theorem tailTrace_5288256 : CollatzResearch.WordTrace tailWord_5288256 prefixEnd_5288256 905139050674322302593253 := by
  unfold tailWord_5288256
  simp only [CollatzResearch.WordTrace]
  refine ⟨96439270964779574532746311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128585694619706099376995081 96439270964779574532746311)
  ·
    refine ⟨144658906447169361799119467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96439270964779574532746311 144658906447169361799119467)
    ·
      refine ⟨216988359670754042698679201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144658906447169361799119467 216988359670754042698679201)
      ·
        refine ⟨162741269753065532024009401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 216988359670754042698679201 162741269753065532024009401)
        ·
          refine ⟨122055952314799149018007051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 162741269753065532024009401 122055952314799149018007051)
          ·
            refine ⟨183083928472198723527010577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122055952314799149018007051 183083928472198723527010577)
            ·
              refine ⟨137312946354149042645257933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 183083928472198723527010577 137312946354149042645257933)
              ·
                refine ⟨51492354882805890991971725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 137312946354149042645257933 51492354882805890991971725)
                ·
                  refine ⟨19309633081052209121989397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51492354882805890991971725 19309633081052209121989397)
                  ·
                    refine ⟨905139050674322302593253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19309633081052209121989397 905139050674322302593253)
                    ·
                      rfl

theorem cell23_5288256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 3, 3, 6].length) (baseStart_5288256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5288256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5288256 prefixEnd_5288256 := by exact prefixLift 5288256
  have htrace : WordTrace (prefixWord ++ tailWord_5288256) baseStart_5288256 baseEnd_5288256 := by
    simpa [prefixWord, tailWord_5288256, baseEnd_5288256] using wordTrace_append hprefix tailTrace_5288256
  have hstable : (prefixWord ++ tailWord_5288256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5288256).length < 2 ^ (prefixWord ++ tailWord_5288256).sum := by decide
  have hdescent : baseEnd_5288256 < baseStart_5288256 := by decide
  rcases family_descends (prefixWord ++ tailWord_5288256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5288290 : List Nat := [3, 3, 2, 1, 1, 2, 3, 1, 1, 6]
def baseStart_5288290 : Nat := 118140960795 + 5288290 * 2 ^ 59
def prefixEnd_5288290 : Nat := 4983230072969 + 3 ^ 40 * 5288290 * 2
def baseEnd_5288290 : Nat := 905144870121739924918201

theorem tailTrace_5288290 : CollatzResearch.WordTrace tailWord_5288290 prefixEnd_5288290 905144870121739924918201 := by
  unfold tailWord_5288290
  simp only [CollatzResearch.WordTrace]
  refine ⟨48219945502858993218057581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128586521340957315248153549 48219945502858993218057581)
  ·
    refine ⟨18082479563572122456771593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48219945502858993218057581 18082479563572122456771593)
    ·
      refine ⟨13561859672679091842578695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18082479563572122456771593 13561859672679091842578695)
      ·
        refine ⟨20342789509018637763868043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13561859672679091842578695 20342789509018637763868043)
        ·
          refine ⟨30514184263527956645802065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20342789509018637763868043 30514184263527956645802065)
          ·
            refine ⟨22885638197645967484351549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30514184263527956645802065 22885638197645967484351549)
            ·
              refine ⟨8582114324117237806631831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22885638197645967484351549 8582114324117237806631831)
              ·
                refine ⟨12873171486175856709947747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8582114324117237806631831 12873171486175856709947747)
                ·
                  refine ⟨19309757229263785064921621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12873171486175856709947747 19309757229263785064921621)
                  ·
                    refine ⟨905144870121739924918201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19309757229263785064921621 905144870121739924918201)
                    ·
                      rfl

theorem cell23_5288290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 3, 1, 1, 6].length) (baseStart_5288290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5288290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5288290 prefixEnd_5288290 := by exact prefixLift 5288290
  have htrace : WordTrace (prefixWord ++ tailWord_5288290) baseStart_5288290 baseEnd_5288290 := by
    simpa [prefixWord, tailWord_5288290, baseEnd_5288290] using wordTrace_append hprefix tailTrace_5288290
  have hstable : (prefixWord ++ tailWord_5288290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5288290).length < 2 ^ (prefixWord ++ tailWord_5288290).sum := by decide
  have hdescent : baseEnd_5288290 < baseStart_5288290 := by decide
  rcases family_descends (prefixWord ++ tailWord_5288290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5288293 : List Nat := [1, 3, 1, 3, 1, 4, 1, 1, 1, 1, 6]
def baseStart_5288293 : Nat := 118140960795 + 5288293 * 2 ^ 59
def prefixEnd_5288293 : Nat := 4983230072969 + 3 ^ 40 * 5288293 * 2
def baseEnd_5288293 : Nat := 2715436150807183263017089

theorem tailTrace_5288293 : CollatzResearch.WordTrace tailWord_5288293 prefixEnd_5288293 2715436150807183263017089 := by
  unfold tailWord_5288293
  simp only [CollatzResearch.WordTrace]
  refine ⟨192879891430425104384589533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128586594286950069589726355 192879891430425104384589533)
  ·
    refine ⟨72329959286409414144221075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 192879891430425104384589533 72329959286409414144221075)
    ·
      refine ⟨108494938929614121216331613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72329959286409414144221075 108494938929614121216331613)
      ·
        refine ⟨40685602098605295456124355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 108494938929614121216331613 40685602098605295456124355)
        ·
          refine ⟨61028403147907943184186533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40685602098605295456124355 61028403147907943184186533)
          ·
            refine ⟨11442825590232739347034975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 61028403147907943184186533 11442825590232739347034975)
            ·
              refine ⟨17164238385349109020552463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11442825590232739347034975 17164238385349109020552463)
              ·
                refine ⟨25746357578023663530828695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17164238385349109020552463 25746357578023663530828695)
                ·
                  refine ⟨38619536367035495296243043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25746357578023663530828695 38619536367035495296243043)
                  ·
                    refine ⟨57929304550553242944364565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 38619536367035495296243043 57929304550553242944364565)
                    ·
                      refine ⟨2715436150807183263017089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 57929304550553242944364565 2715436150807183263017089)
                      ·
                        rfl

theorem cell23_5288293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 1, 1, 1, 1, 6].length) (baseStart_5288293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5288293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5288293 prefixEnd_5288293 := by exact prefixLift 5288293
  have htrace : WordTrace (prefixWord ++ tailWord_5288293) baseStart_5288293 baseEnd_5288293 := by
    simpa [prefixWord, tailWord_5288293, baseEnd_5288293] using wordTrace_append hprefix tailTrace_5288293
  have hstable : (prefixWord ++ tailWord_5288293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5288293).length < 2 ^ (prefixWord ++ tailWord_5288293).sum := by decide
  have hdescent : baseEnd_5288293 < baseStart_5288293 := by decide
  rcases family_descends (prefixWord ++ tailWord_5288293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5288313 : List Nat := [1, 2, 1, 3, 2, 1, 1, 3, 3, 3, 3]
def baseStart_5288313 : Nat := 118140960795 + 5288313 * 2 ^ 59
def prefixEnd_5288313 : Nat := 4983230072969 + 3 ^ 40 * 5288313 * 2
def baseEnd_5288313 : Nat := 2715446420420273184766997

theorem tailTrace_5288313 : CollatzResearch.WordTrace tailWord_5288313 prefixEnd_5288313 2715446420420273184766997 := by
  unfold tailWord_5288313
  simp only [CollatzResearch.WordTrace]
  refine ⟨192880620890352647800317593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128587080593568431866878395 192880620890352647800317593)
  ·
    refine ⟨144660465667764485850238195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192880620890352647800317593 144660465667764485850238195)
    ·
      refine ⟨216990698501646728775357293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144660465667764485850238195 216990698501646728775357293)
      ·
        refine ⟨81371511938117523290758985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 216990698501646728775357293 81371511938117523290758985)
        ·
          refine ⟨61028633953588142468069239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81371511938117523290758985 61028633953588142468069239)
          ·
            refine ⟨91542950930382213702103859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61028633953588142468069239 91542950930382213702103859)
            ·
              refine ⟨137314426395573320553155789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91542950930382213702103859 137314426395573320553155789)
              ·
                refine ⟨51492909898339995207433421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 137314426395573320553155789 51492909898339995207433421)
                ·
                  refine ⟨19309841211877498202787533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51492909898339995207433421 19309841211877498202787533)
                  ·
                    refine ⟨7241190454454061826045325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19309841211877498202787533 7241190454454061826045325)
                    ·
                      refine ⟨2715446420420273184766997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7241190454454061826045325 2715446420420273184766997)
                      ·
                        rfl

theorem cell23_5288313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 3, 3, 3, 3].length) (baseStart_5288313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5288313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5288313 prefixEnd_5288313 := by exact prefixLift 5288313
  have htrace : WordTrace (prefixWord ++ tailWord_5288313) baseStart_5288313 baseEnd_5288313 := by
    simpa [prefixWord, tailWord_5288313, baseEnd_5288313] using wordTrace_append hprefix tailTrace_5288313
  have hstable : (prefixWord ++ tailWord_5288313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5288313).length < 2 ^ (prefixWord ++ tailWord_5288313).sum := by decide
  have hdescent : baseEnd_5288313 < baseStart_5288313 := by decide
  rcases family_descends (prefixWord ++ tailWord_5288313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5288331 : List Nat := [1, 1, 1, 1, 4, 5, 3, 2, 1, 2, 2]
def baseStart_5288331 : Nat := 118140960795 + 5288331 * 2 ^ 59
def prefixEnd_5288331 : Nat := 4983230072969 + 3 ^ 40 * 5288331 * 2
def baseEnd_5288331 : Nat := 2715455663072054114341915

theorem tailTrace_5288331 : CollatzResearch.WordTrace tailWord_5288331 prefixEnd_5288331 2715455663072054114341915 := by
  unfold tailWord_5288331
  simp only [CollatzResearch.WordTrace]
  refine ⟨192881277404287436874472847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128587518269524957916315231 192881277404287436874472847)
  ·
    refine ⟨289321916106431155311709271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192881277404287436874472847 289321916106431155311709271)
    ·
      refine ⟨433982874159646732967563907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 289321916106431155311709271 433982874159646732967563907)
      ·
        refine ⟨650974311239470099451345861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 433982874159646732967563907 650974311239470099451345861)
        ·
          refine ⟨122057683357400643647127349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 650974311239470099451345861 122057683357400643647127349)
          ·
            refine ⟨11442907814756310341918189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 122057683357400643647127349 11442907814756310341918189)
            ·
              refine ⟨4291090430533616378219321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11442907814756310341918189 4291090430533616378219321)
              ·
                refine ⟨3218317822900212283664491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4291090430533616378219321 3218317822900212283664491)
                ·
                  refine ⟨4827476734350318425496737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3218317822900212283664491 4827476734350318425496737)
                  ·
                    refine ⟨3620607550762738819122553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4827476734350318425496737 3620607550762738819122553)
                    ·
                      refine ⟨2715455663072054114341915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3620607550762738819122553 2715455663072054114341915)
                      ·
                        rfl

theorem cell23_5288331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 3, 2, 1, 2, 2].length) (baseStart_5288331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5288331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5288331 prefixEnd_5288331 := by exact prefixLift 5288331
  have htrace : WordTrace (prefixWord ++ tailWord_5288331) baseStart_5288331 baseEnd_5288331 := by
    simpa [prefixWord, tailWord_5288331, baseEnd_5288331] using wordTrace_append hprefix tailTrace_5288331
  have hstable : (prefixWord ++ tailWord_5288331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5288331).length < 2 ^ (prefixWord ++ tailWord_5288331).sum := by decide
  have hdescent : baseEnd_5288331 < baseStart_5288331 := by decide
  rcases family_descends (prefixWord ++ tailWord_5288331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5288404 : List Nat := [2, 4, 1, 2, 2, 2, 2, 1, 1, 4, 2]
def baseStart_5288404 : Nat := 118140960795 + 5288404 * 2 ^ 59
def prefixEnd_5288404 : Nat := 4983230072969 + 3 ^ 40 * 5288404 * 2
def baseEnd_5288404 : Nat := 2715493147159832328729079

theorem tailTrace_5288404 : CollatzResearch.WordTrace tailWord_5288404 prefixEnd_5288404 2715493147159832328729079 := by
  unfold tailWord_5288404
  simp only [CollatzResearch.WordTrace]
  refine ⟨96441969966511485170940133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128589293288681980227920177 96441969966511485170940133)
  ·
    refine ⟨18082869368720903469551275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 96441969966511485170940133 18082869368720903469551275)
    ·
      refine ⟨27124304053081355204326913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18082869368720903469551275 27124304053081355204326913)
      ·
        refine ⟨20343228039811016403245185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27124304053081355204326913 20343228039811016403245185)
        ·
          refine ⟨15257421029858262302433889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20343228039811016403245185 15257421029858262302433889)
          ·
            refine ⟨11443065772393696726825417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15257421029858262302433889 11443065772393696726825417)
            ·
              refine ⟨8582299329295272545119063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11443065772393696726825417 8582299329295272545119063)
              ·
                refine ⟨12873448993942908817678595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8582299329295272545119063 12873448993942908817678595)
                ·
                  refine ⟨19310173490914363226517893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12873448993942908817678595 19310173490914363226517893)
                  ·
                    refine ⟨3620657529546443104972105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19310173490914363226517893 3620657529546443104972105)
                    ·
                      refine ⟨2715493147159832328729079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3620657529546443104972105 2715493147159832328729079)
                      ·
                        rfl

theorem cell23_5288404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 2, 1, 1, 4, 2].length) (baseStart_5288404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5288404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5288404 prefixEnd_5288404 := by exact prefixLift 5288404
  have htrace : WordTrace (prefixWord ++ tailWord_5288404) baseStart_5288404 baseEnd_5288404 := by
    simpa [prefixWord, tailWord_5288404, baseEnd_5288404] using wordTrace_append hprefix tailTrace_5288404
  have hstable : (prefixWord ++ tailWord_5288404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5288404).length < 2 ^ (prefixWord ++ tailWord_5288404).sum := by decide
  have hdescent : baseEnd_5288404 < baseStart_5288404 := by decide
  rcases family_descends (prefixWord ++ tailWord_5288404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5288443 : List Nat := [1, 1, 1, 1, 1, 3, 2, 1, 5, 3, 4]
def baseStart_5288443 : Nat := 118140960795 + 5288443 * 2 ^ 59
def prefixEnd_5288443 : Nat := 4983230072969 + 3 ^ 40 * 5288443 * 2
def baseEnd_5288443 : Nat := 2715513172905357676141399

theorem tailTrace_5288443 : CollatzResearch.WordTrace tailWord_5288443 prefixEnd_5288443 2715513172905357676141399 := by
  unfold tailWord_5288443
  simp only [CollatzResearch.WordTrace]
  refine ⟨192885362379881680002549983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128590241586587786668366655 192885362379881680002549983)
  ·
    refine ⟨289328043569822520003824975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192885362379881680002549983 289328043569822520003824975)
    ·
      refine ⟨433992065354733780005737463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 289328043569822520003824975 433992065354733780005737463)
      ·
        refine ⟨650988098032100670008606195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 433992065354733780005737463 650988098032100670008606195)
        ·
          refine ⟨976482147048151005012909293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 650988098032100670008606195 976482147048151005012909293)
          ·
            refine ⟨366180805143056626879840985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 976482147048151005012909293 366180805143056626879840985)
            ·
              refine ⟨274635603857292470159880739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 366180805143056626879840985 274635603857292470159880739)
              ·
                refine ⟨411953405785938705239821109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 274635603857292470159880739 411953405785938705239821109)
                ·
                  refine ⟨38620631792431753616233229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 411953405785938705239821109 38620631792431753616233229)
                  ·
                    refine ⟨14482736922161907606087461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 38620631792431753616233229 14482736922161907606087461)
                    ·
                      refine ⟨2715513172905357676141399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14482736922161907606087461 2715513172905357676141399)
                      ·
                        rfl

theorem cell23_5288443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 5, 3, 4].length) (baseStart_5288443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5288443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5288443 prefixEnd_5288443 := by exact prefixLift 5288443
  have htrace : WordTrace (prefixWord ++ tailWord_5288443) baseStart_5288443 baseEnd_5288443 := by
    simpa [prefixWord, tailWord_5288443, baseEnd_5288443] using wordTrace_append hprefix tailTrace_5288443
  have hstable : (prefixWord ++ tailWord_5288443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5288443).length < 2 ^ (prefixWord ++ tailWord_5288443).sum := by decide
  have hdescent : baseEnd_5288443 < baseStart_5288443 := by decide
  rcases family_descends (prefixWord ++ tailWord_5288443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5288460 : List Nat := [2, 2, 1, 2, 4, 1, 1, 2, 1, 3, 4]
def baseStart_5288460 : Nat := 118140960795 + 5288460 * 2 ^ 59
def prefixEnd_5288460 : Nat := 4983230072969 + 3 ^ 40 * 5288460 * 2
def baseEnd_5288460 : Nat := 2715521902076484109628821

theorem tailTrace_5288460 : CollatzResearch.WordTrace tailWord_5288460 prefixEnd_5288460 2715521902076484109628821 := by
  unfold tailWord_5288460
  simp only [CollatzResearch.WordTrace]
  refine ⟨96442991210410045952959417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128590654947213394603945889 96442991210410045952959417)
  ·
    refine ⟨72332243407807534464719563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96442991210410045952959417 72332243407807534464719563)
    ·
      refine ⟨108498365111711301697079345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72332243407807534464719563 108498365111711301697079345)
      ·
        refine ⟨81373773833783476272809509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108498365111711301697079345 81373773833783476272809509)
        ·
          refine ⟨15257582593834401801151783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 81373773833783476272809509 15257582593834401801151783)
          ·
            refine ⟨22886373890751602701727675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15257582593834401801151783 22886373890751602701727675)
            ·
              refine ⟨34329560836127404052591513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22886373890751602701727675 34329560836127404052591513)
              ·
                refine ⟨25747170627095553039443635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34329560836127404052591513 25747170627095553039443635)
                ·
                  refine ⟨38620755940643329559165453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25747170627095553039443635 38620755940643329559165453)
                  ·
                    refine ⟨14482783477741248584687045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 38620755940643329559165453 14482783477741248584687045)
                    ·
                      refine ⟨2715521902076484109628821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14482783477741248584687045 2715521902076484109628821)
                      ·
                        rfl

theorem cell23_5288460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 2, 1, 3, 4].length) (baseStart_5288460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5288460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5288460 prefixEnd_5288460 := by exact prefixLift 5288460
  have htrace : WordTrace (prefixWord ++ tailWord_5288460) baseStart_5288460 baseEnd_5288460 := by
    simpa [prefixWord, tailWord_5288460, baseEnd_5288460] using wordTrace_append hprefix tailTrace_5288460
  have hstable : (prefixWord ++ tailWord_5288460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5288460).length < 2 ^ (prefixWord ++ tailWord_5288460).sum := by decide
  have hdescent : baseEnd_5288460 < baseStart_5288460 := by decide
  rcases family_descends (prefixWord ++ tailWord_5288460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5288473 : List Nat := [1, 2, 1, 2, 1, 1, 2, 2, 4, 1, 6]
def baseStart_5288473 : Nat := 118140960795 + 5288473 * 2 ^ 59
def prefixEnd_5288473 : Nat := 4983230072969 + 3 ^ 40 * 5288473 * 2
def baseEnd_5288473 : Nat := 2715528577324992558766261

theorem tailTrace_5288473 : CollatzResearch.WordTrace tailWord_5288473 prefixEnd_5288473 2715528577324992558766261 := by
  unfold tailWord_5288473
  simp only [CollatzResearch.WordTrace]
  refine ⟨192886456569772995126142073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128590971046515330084094715 192886456569772995126142073)
  ·
    refine ⟨144664842427329746344606555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192886456569772995126142073 144664842427329746344606555)
    ·
      refine ⟨216997263640994619516909833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144664842427329746344606555 216997263640994619516909833)
      ·
        refine ⟨162747947730745964637682375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 216997263640994619516909833 162747947730745964637682375)
        ·
          refine ⟨244121921596118946956523563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162747947730745964637682375 244121921596118946956523563)
          ·
            refine ⟨366182882394178420434785345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 244121921596118946956523563 366182882394178420434785345)
            ·
              refine ⟨274637161795633815326089009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 366182882394178420434785345 274637161795633815326089009)
              ·
                refine ⟨205977871346725361494566757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 274637161795633815326089009 205977871346725361494566757)
                ·
                  refine ⟨38620850877511005280231267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 205977871346725361494566757 38620850877511005280231267)
                  ·
                    refine ⟨57931276316266507920346901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 38620850877511005280231267 57931276316266507920346901)
                    ·
                      refine ⟨2715528577324992558766261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 57931276316266507920346901 2715528577324992558766261)
                      ·
                        rfl

theorem cell23_5288473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 2, 4, 1, 6].length) (baseStart_5288473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5288473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5288473 prefixEnd_5288473 := by exact prefixLift 5288473
  have htrace : WordTrace (prefixWord ++ tailWord_5288473) baseStart_5288473 baseEnd_5288473 := by
    simpa [prefixWord, tailWord_5288473, baseEnd_5288473] using wordTrace_append hprefix tailTrace_5288473
  have hstable : (prefixWord ++ tailWord_5288473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5288473).length < 2 ^ (prefixWord ++ tailWord_5288473).sum := by decide
  have hdescent : baseEnd_5288473 < baseStart_5288473 := by decide
  rcases family_descends (prefixWord ++ tailWord_5288473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5288494 : List Nat := [4, 1, 3, 1, 3, 1, 1, 2, 2, 1, 4]
def baseStart_5288494 : Nat := 118140960795 + 5288494 * 2 ^ 59
def prefixEnd_5288494 : Nat := 4983230072969 + 3 ^ 40 * 5288494 * 2
def baseEnd_5288494 : Nat := 2715539360418736976603665

theorem tailTrace_5288494 : CollatzResearch.WordTrace tailWord_5288494 prefixEnd_5288494 2715539360418736976603665 := by
  unfold tailWord_5288494
  simp only [CollatzResearch.WordTrace]
  refine ⟨24110902812837114464082067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 128591481668464610475104357 24110902812837114464082067)
  ·
    refine ⟨36166354219255671696123101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24110902812837114464082067 36166354219255671696123101)
    ·
      refine ⟨13562382832220876886046163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36166354219255671696123101 13562382832220876886046163)
      ·
        refine ⟨20343574248331315329069245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13562382832220876886046163 20343574248331315329069245)
        ·
          refine ⟨7628840343124243248400967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20343574248331315329069245 7628840343124243248400967)
          ·
            refine ⟨11443260514686364872601451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7628840343124243248400967 11443260514686364872601451)
            ·
              refine ⟨17164890772029547308902177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11443260514686364872601451 17164890772029547308902177)
              ·
                refine ⟨12873668079022160481676633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17164890772029547308902177 12873668079022160481676633)
                ·
                  refine ⟨9655251059266620361257475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12873668079022160481676633 9655251059266620361257475)
                  ·
                    refine ⟨14482876588899930541886213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9655251059266620361257475 14482876588899930541886213)
                    ·
                      refine ⟨2715539360418736976603665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14482876588899930541886213 2715539360418736976603665)
                      ·
                        rfl

theorem cell23_5288494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 1, 2, 2, 1, 4].length) (baseStart_5288494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5288494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5288494 prefixEnd_5288494 := by exact prefixLift 5288494
  have htrace : WordTrace (prefixWord ++ tailWord_5288494) baseStart_5288494 baseEnd_5288494 := by
    simpa [prefixWord, tailWord_5288494, baseEnd_5288494] using wordTrace_append hprefix tailTrace_5288494
  have hstable : (prefixWord ++ tailWord_5288494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5288494).length < 2 ^ (prefixWord ++ tailWord_5288494).sum := by decide
  have hdescent : baseEnd_5288494 < baseStart_5288494 := by decide
  rcases family_descends (prefixWord ++ tailWord_5288494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5288517 : List Nat := [1, 3, 1, 1, 1, 5, 4, 1, 6]
def baseStart_5288517 : Nat := 118140960795 + 5288517 * 2 ^ 59
def prefixEnd_5288517 : Nat := 4983230072969 + 3 ^ 40 * 5288517 * 2
def baseEnd_5288517 : Nat := 301727907830421154068451

theorem tailTrace_5288517 : CollatzResearch.WordTrace tailWord_5288517 prefixEnd_5288517 301727907830421154068451 := by
  unfold tailWord_5288517
  simp only [CollatzResearch.WordTrace]
  refine ⟨192888061381613590640743805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128592040921075727093829203 192888061381613590640743805)
  ·
    refine ⟨72333023018105096490278927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 192888061381613590640743805 72333023018105096490278927)
    ·
      refine ⟨108499534527157644735418391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72333023018105096490278927 108499534527157644735418391)
      ·
        refine ⟨162749301790736467103127587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108499534527157644735418391 162749301790736467103127587)
        ·
          refine ⟨244123952686104700654691381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162749301790736467103127587 244123952686104700654691381)
          ·
            refine ⟨22886620564322315686377317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 244123952686104700654691381 22886620564322315686377317)
            ·
              refine ⟨4291241355810434191195747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22886620564322315686377317 4291241355810434191195747)
              ·
                refine ⟨6436862033715651286793621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4291241355810434191195747 6436862033715651286793621)
                ·
                  refine ⟨301727907830421154068451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6436862033715651286793621 301727907830421154068451)
                  ·
                    rfl

theorem cell23_5288517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 4, 1, 6].length) (baseStart_5288517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5288517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5288517 prefixEnd_5288517 := by exact prefixLift 5288517
  have htrace : WordTrace (prefixWord ++ tailWord_5288517) baseStart_5288517 baseEnd_5288517 := by
    simpa [prefixWord, tailWord_5288517, baseEnd_5288517] using wordTrace_append hprefix tailTrace_5288517
  have hstable : (prefixWord ++ tailWord_5288517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5288517).length < 2 ^ (prefixWord ++ tailWord_5288517).sum := by decide
  have hdescent : baseEnd_5288517 < baseStart_5288517 := by decide
  rcases family_descends (prefixWord ++ tailWord_5288517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5288527 : List Nat := [1, 1, 2, 1, 1, 2, 4, 4, 3, 1, 3]
def baseStart_5288527 : Nat := 118140960795 + 5288527 * 2 ^ 59
def prefixEnd_5288527 : Nat := 4983230072969 + 3 ^ 40 * 5288527 * 2
def baseEnd_5288527 : Nat := 2715556305280335347491013

theorem tailTrace_5288527 : CollatzResearch.WordTrace tailWord_5288527 prefixEnd_5288527 2715556305280335347491013 := by
  unfold tailWord_5288527
  simp only [CollatzResearch.WordTrace]
  refine ⟨192888426111577362348607835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128592284074384908232405223 192888426111577362348607835)
  ·
    refine ⟨289332639167366043522911753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192888426111577362348607835 289332639167366043522911753)
    ·
      refine ⟨216999479375524532642183815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 289332639167366043522911753 216999479375524532642183815)
      ·
        refine ⟨325499219063286798963275723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 216999479375524532642183815 325499219063286798963275723)
        ·
          refine ⟨488248828594930198444913585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 325499219063286798963275723 488248828594930198444913585)
          ·
            refine ⟨366186621446197648833685189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 488248828594930198444913585 366186621446197648833685189)
            ·
              refine ⟨68659991521162059156315973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 366186621446197648833685189 68659991521162059156315973)
              ·
                refine ⟨12873748410217886091809245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 68659991521162059156315973 12873748410217886091809245)
                ·
                  refine ⟨4827655653831707284428467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12873748410217886091809245 4827655653831707284428467)
                  ·
                    refine ⟨7241483480747560926642701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4827655653831707284428467 7241483480747560926642701)
                    ·
                      refine ⟨2715556305280335347491013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7241483480747560926642701 2715556305280335347491013)
                      ·
                        rfl

theorem cell23_5288527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 4, 3, 1, 3].length) (baseStart_5288527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5288527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5288527 prefixEnd_5288527 := by exact prefixLift 5288527
  have htrace : WordTrace (prefixWord ++ tailWord_5288527) baseStart_5288527 baseEnd_5288527 := by
    simpa [prefixWord, tailWord_5288527, baseEnd_5288527] using wordTrace_append hprefix tailTrace_5288527
  have hstable : (prefixWord ++ tailWord_5288527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5288527).length < 2 ^ (prefixWord ++ tailWord_5288527).sum := by decide
  have hdescent : baseEnd_5288527 < baseStart_5288527 := by decide
  rcases family_descends (prefixWord ++ tailWord_5288527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5288554 : List Nat := [3, 1, 3, 2, 1, 1, 1, 4, 2, 3, 2]
def baseStart_5288554 : Nat := 118140960795 + 5288554 * 2 ^ 59
def prefixEnd_5288554 : Nat := 4983230072969 + 3 ^ 40 * 5288554 * 2
def baseEnd_5288554 : Nat := 2715570169258006741853389

theorem tailTrace_5288554 : CollatzResearch.WordTrace tailWord_5288554 prefixEnd_5288554 2715570169258006741853389 := by
  unfold tailWord_5288554
  simp only [CollatzResearch.WordTrace]
  refine ⟨48222352720619886489960179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128592940588319697306560477 48222352720619886489960179)
  ·
    refine ⟨72333529080929829734940269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48222352720619886489960179 72333529080929829734940269)
    ·
      refine ⟨27125073405348686150602601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72333529080929829734940269 27125073405348686150602601)
      ·
        refine ⟨20343805054011514612951951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27125073405348686150602601 20343805054011514612951951)
        ·
          refine ⟨30515707581017271919427927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20343805054011514612951951 30515707581017271919427927)
          ·
            refine ⟨45773561371525907879141891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30515707581017271919427927 45773561371525907879141891)
            ·
              refine ⟨68660342057288861818712837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45773561371525907879141891 68660342057288861818712837)
              ·
                refine ⟨12873814135741661591008657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 68660342057288861818712837 12873814135741661591008657)
                ·
                  refine ⟨9655360601806246193256493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12873814135741661591008657 9655360601806246193256493)
                  ·
                    refine ⟨3620760225677342322471185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9655360601806246193256493 3620760225677342322471185)
                    ·
                      refine ⟨2715570169258006741853389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3620760225677342322471185 2715570169258006741853389)
                      ·
                        rfl

theorem cell23_5288554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 4, 2, 3, 2].length) (baseStart_5288554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5288554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5288554 prefixEnd_5288554 := by exact prefixLift 5288554
  have htrace : WordTrace (prefixWord ++ tailWord_5288554) baseStart_5288554 baseEnd_5288554 := by
    simpa [prefixWord, tailWord_5288554, baseEnd_5288554] using wordTrace_append hprefix tailTrace_5288554
  have hstable : (prefixWord ++ tailWord_5288554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5288554).length < 2 ^ (prefixWord ++ tailWord_5288554).sum := by decide
  have hdescent : baseEnd_5288554 < baseStart_5288554 := by decide
  rcases family_descends (prefixWord ++ tailWord_5288554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5288577 : List Nat := [1, 2, 4, 2, 1, 1, 4, 1, 1, 6]
def baseStart_5288577 : Nat := 118140960795 + 5288577 * 2 ^ 59
def prefixEnd_5288577 : Nat := 4983230072969 + 3 ^ 40 * 5288577 * 2
def baseEnd_5288577 : Nat := 905193993104353383955261

theorem tailTrace_5288577 : CollatzResearch.WordTrace tailWord_5288577 prefixEnd_5288577 905193993104353383955261 := by
  unfold tailWord_5288577
  simp only [CollatzResearch.WordTrace]
  refine ⟨192890249761396220887927985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128593499840930813925285323 192890249761396220887927985)
  ·
    refine ⟨144667687321047165665945989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192890249761396220887927985 144667687321047165665945989)
    ·
      refine ⟨27125191372696343562364873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 144667687321047165665945989 27125191372696343562364873)
      ·
        refine ⟨20343893529522257671773655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27125191372696343562364873 20343893529522257671773655)
        ·
          refine ⟨30515840294283386507660483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20343893529522257671773655 30515840294283386507660483)
          ·
            refine ⟨45773760441425079761490725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30515840294283386507660483 45773760441425079761490725)
            ·
              refine ⟨8582580082767202455279511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45773760441425079761490725 8582580082767202455279511)
              ·
                refine ⟨12873870124150803682919267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8582580082767202455279511 12873870124150803682919267)
                ·
                  refine ⟨19310805186226205524378901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12873870124150803682919267 19310805186226205524378901)
                  ·
                    refine ⟨905193993104353383955261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19310805186226205524378901 905193993104353383955261)
                    ·
                      rfl

theorem cell23_5288577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 4, 1, 1, 6].length) (baseStart_5288577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5288577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5288577 prefixEnd_5288577 := by exact prefixLift 5288577
  have htrace : WordTrace (prefixWord ++ tailWord_5288577) baseStart_5288577 baseEnd_5288577 := by
    simpa [prefixWord, tailWord_5288577, baseEnd_5288577] using wordTrace_append hprefix tailTrace_5288577
  have hstable : (prefixWord ++ tailWord_5288577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5288577).length < 2 ^ (prefixWord ++ tailWord_5288577).sum := by decide
  have hdescent : baseEnd_5288577 < baseStart_5288577 := by decide
  rcases family_descends (prefixWord ++ tailWord_5288577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5288631 : List Nat := [1, 1, 3, 1, 7, 1, 1, 1, 1, 2, 4]
def baseStart_5288631 : Nat := 118140960795 + 5288631 * 2 ^ 59
def prefixEnd_5288631 : Nat := 4983230072969 + 3 ^ 40 * 5288631 * 2
def baseEnd_5288631 : Nat := 2715609707268402940590535

theorem tailTrace_5288631 : CollatzResearch.WordTrace tailWord_5288631 prefixEnd_5288631 2715609707268402940590535 := by
  unfold tailWord_5288631
  simp only [CollatzResearch.WordTrace]
  refine ⟨192892219303200588110393747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128594812868800392073595831 192892219303200588110393747)
  ·
    refine ⟨289338328954800882165590621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192892219303200588110393747 289338328954800882165590621)
    ·
      refine ⟨108501873358050330812096483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 289338328954800882165590621 108501873358050330812096483)
      ·
        refine ⟨162752810037075496218144725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108501873358050330812096483 162752810037075496218144725)
        ·
          refine ⟨3814518985243956942612767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 162752810037075496218144725 3814518985243956942612767)
          ·
            refine ⟨5721778477865935413919151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3814518985243956942612767 5721778477865935413919151)
            ·
              refine ⟨8582667716798903120878727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5721778477865935413919151 8582667716798903120878727)
              ·
                refine ⟨12874001575198354681318091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8582667716798903120878727 12874001575198354681318091)
                ·
                  refine ⟨19311002362797532021977137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12874001575198354681318091 19311002362797532021977137)
                  ·
                    refine ⟨14483251772098149016482853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19311002362797532021977137 14483251772098149016482853)
                    ·
                      refine ⟨2715609707268402940590535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14483251772098149016482853 2715609707268402940590535)
                      ·
                        rfl

theorem cell23_5288631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 1, 1, 1, 2, 4].length) (baseStart_5288631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5288631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5288631 prefixEnd_5288631 := by exact prefixLift 5288631
  have htrace : WordTrace (prefixWord ++ tailWord_5288631) baseStart_5288631 baseEnd_5288631 := by
    simpa [prefixWord, tailWord_5288631, baseEnd_5288631] using wordTrace_append hprefix tailTrace_5288631
  have hstable : (prefixWord ++ tailWord_5288631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5288631).length < 2 ^ (prefixWord ++ tailWord_5288631).sum := by decide
  have hdescent : baseEnd_5288631 < baseStart_5288631 := by decide
  rcases family_descends (prefixWord ++ tailWord_5288631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5288707 : List Nat := [1, 1, 1, 3, 2, 2, 1, 2, 4, 3, 3]
def baseStart_5288707 : Nat := 118140960795 + 5288707 * 2 ^ 59
def prefixEnd_5288707 : Nat := 4983230072969 + 3 ^ 40 * 5288707 * 2
def baseEnd_5288707 : Nat := 2715648731798144643240185

theorem tailTrace_5288707 : CollatzResearch.WordTrace tailWord_5288707 prefixEnd_5288707 2715648731798144643240185 := by
  unfold tailWord_5288707
  simp only [CollatzResearch.WordTrace]
  refine ⟨192894991250925253090160375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128596660833950168726773583 192894991250925253090160375)
  ·
    refine ⟨289342486876387879635240563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192894991250925253090160375 289342486876387879635240563)
    ·
      refine ⟨434013730314581819452860845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 289342486876387879635240563 434013730314581819452860845)
      ·
        refine ⟨162755148867968182294822817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 434013730314581819452860845 162755148867968182294822817)
        ·
          refine ⟨122066361650976136721117113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 162755148867968182294822817 122066361650976136721117113)
          ·
            refine ⟨91549771238232102540837835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 122066361650976136721117113 91549771238232102540837835)
            ·
              refine ⟨137324656857348153811256753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91549771238232102540837835 137324656857348153811256753)
              ·
                refine ⟨102993492643011115358442565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 137324656857348153811256753 102993492643011115358442565)
                ·
                  refine ⟨19311279870564584129707981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 102993492643011115358442565 19311279870564584129707981)
                  ·
                    refine ⟨7241729951461719048640493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19311279870564584129707981 7241729951461719048640493)
                    ·
                      refine ⟨2715648731798144643240185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7241729951461719048640493 2715648731798144643240185)
                      ·
                        rfl

theorem cell23_5288707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 2, 4, 3, 3].length) (baseStart_5288707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5288707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5288707 prefixEnd_5288707 := by exact prefixLift 5288707
  have htrace : WordTrace (prefixWord ++ tailWord_5288707) baseStart_5288707 baseEnd_5288707 := by
    simpa [prefixWord, tailWord_5288707, baseEnd_5288707] using wordTrace_append hprefix tailTrace_5288707
  have hstable : (prefixWord ++ tailWord_5288707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5288707).length < 2 ^ (prefixWord ++ tailWord_5288707).sum := by decide
  have hdescent : baseEnd_5288707 < baseStart_5288707 := by decide
  rcases family_descends (prefixWord ++ tailWord_5288707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5288714 : List Nat := [3, 1, 2, 2, 1, 2, 2, 5, 5]
def baseStart_5288714 : Nat := 118140960795 + 5288714 * 2 ^ 59
def prefixEnd_5288714 : Nat := 4983230072969 + 3 ^ 40 * 5288714 * 2
def baseEnd_5288714 : Nat := 301739147351414012872517

theorem tailTrace_5288714 : CollatzResearch.WordTrace tailWord_5288714 prefixEnd_5288714 301739147351414012872517 := by
  unfold tailWord_5288714
  simp only [CollatzResearch.WordTrace]
  refine ⟨48223811640474973321416299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128596831041266595523776797 48223811640474973321416299)
  ·
    refine ⟨72335717460712459982124449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48223811640474973321416299 72335717460712459982124449)
    ·
      refine ⟨54251788095534344986593337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72335717460712459982124449 54251788095534344986593337)
      ·
        refine ⟨40688841071650758739945003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54251788095534344986593337 40688841071650758739945003)
        ·
          refine ⟨61033261607476138109917505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40688841071650758739945003 61033261607476138109917505)
          ·
            refine ⟨45774946205607103582438129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61033261607476138109917505 45774946205607103582438129)
            ·
              refine ⟨34331209654205327686828597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45774946205607103582438129 34331209654205327686828597)
              ·
                refine ⟨3218550905081749470640181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34331209654205327686828597 3218550905081749470640181)
                ·
                  refine ⟨301739147351414012872517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3218550905081749470640181 301739147351414012872517)
                  ·
                    rfl

theorem cell23_5288714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 5, 5].length) (baseStart_5288714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5288714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5288714 prefixEnd_5288714 := by exact prefixLift 5288714
  have htrace : WordTrace (prefixWord ++ tailWord_5288714) baseStart_5288714 baseEnd_5288714 := by
    simpa [prefixWord, tailWord_5288714, baseEnd_5288714] using wordTrace_append hprefix tailTrace_5288714
  have hstable : (prefixWord ++ tailWord_5288714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5288714).length < 2 ^ (prefixWord ++ tailWord_5288714).sum := by decide
  have hdescent : baseEnd_5288714 < baseStart_5288714 := by decide
  rcases family_descends (prefixWord ++ tailWord_5288714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5288737 : List Nat := [1, 2, 3, 2, 1, 2, 1, 3, 1, 2, 5]
def baseStart_5288737 : Nat := 118140960795 + 5288737 * 2 ^ 59
def prefixEnd_5288737 : Nat := 4983230072969 + 3 ^ 40 * 5288737 * 2
def baseEnd_5288737 : Nat := 2715664136217779525865047

theorem tailTrace_5288737 : CollatzResearch.WordTrace tailWord_5288737 prefixEnd_5288737 2715664136217779525865047 := by
  unfold tailWord_5288737
  simp only [CollatzResearch.WordTrace]
  refine ⟨192896085440816568213752465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128597390293877712142501643 192896085440816568213752465)
  ·
    refine ⟨144672064080612426160314349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192896085440816568213752465 144672064080612426160314349)
    ·
      refine ⟨54252024030229659810117881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 144672064080612426160314349 54252024030229659810117881)
      ·
        refine ⟨40689018022672244857588411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54252024030229659810117881 40689018022672244857588411)
        ·
          refine ⟨61033527034008367286382617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40689018022672244857588411 61033527034008367286382617)
          ·
            refine ⟨45775145275506275464786963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61033527034008367286382617 45775145275506275464786963)
            ·
              refine ⟨68662717913259413197180445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45775145275506275464786963 68662717913259413197180445)
              ·
                refine ⟨25748519217472279948942667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 68662717913259413197180445 25748519217472279948942667)
                ·
                  refine ⟨38622778826208419923414001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25748519217472279948942667 38622778826208419923414001)
                  ·
                    refine ⟨28967084119656314942560501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 38622778826208419923414001 28967084119656314942560501)
                    ·
                      refine ⟨2715664136217779525865047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28967084119656314942560501 2715664136217779525865047)
                      ·
                        rfl

theorem cell23_5288737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 3, 1, 2, 5].length) (baseStart_5288737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5288737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5288737 prefixEnd_5288737 := by exact prefixLift 5288737
  have htrace : WordTrace (prefixWord ++ tailWord_5288737) baseStart_5288737 baseEnd_5288737 := by
    simpa [prefixWord, tailWord_5288737, baseEnd_5288737] using wordTrace_append hprefix tailTrace_5288737
  have hstable : (prefixWord ++ tailWord_5288737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5288737).length < 2 ^ (prefixWord ++ tailWord_5288737).sum := by decide
  have hdescent : baseEnd_5288737 < baseStart_5288737 := by decide
  rcases family_descends (prefixWord ++ tailWord_5288737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5288747 : List Nat := [1, 1, 1, 1, 2, 1, 2, 3, 6, 1, 4]
def baseStart_5288747 : Nat := 118140960795 + 5288747 * 2 ^ 59
def prefixEnd_5288747 : Nat := 4983230072969 + 3 ^ 40 * 5288747 * 2
def baseEnd_5288747 : Nat := 2715669271024324486740001

theorem tailTrace_5288747 : CollatzResearch.WordTrace tailWord_5288747 prefixEnd_5288747 2715669271024324486740001 := by
  unfold tailWord_5288747
  simp only [CollatzResearch.WordTrace]
  refine ⟨192896450170780339921616495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128597633447186893281077663 192896450170780339921616495)
  ·
    refine ⟨289344675256170509882424743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192896450170780339921616495 289344675256170509882424743)
    ·
      refine ⟨434017012884255764823637115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 289344675256170509882424743 434017012884255764823637115)
      ·
        refine ⟨651025519326383647235455673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 434017012884255764823637115 651025519326383647235455673)
        ·
          refine ⟨488269139494787735426591755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 651025519326383647235455673 488269139494787735426591755)
          ·
            refine ⟨732403709242181603139887633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 488269139494787735426591755 732403709242181603139887633)
            ·
              refine ⟨549302781931636202354915725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 732403709242181603139887633 549302781931636202354915725)
              ·
                refine ⟨205988543224363575883093397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 549302781931636202354915725 205988543224363575883093397)
                ·
                  refine ⟨9655712963642042619520003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 205988543224363575883093397 9655712963642042619520003)
                  ·
                    refine ⟨14483569445463063929280005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9655712963642042619520003 14483569445463063929280005)
                    ·
                      refine ⟨2715669271024324486740001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14483569445463063929280005 2715669271024324486740001)
                      ·
                        rfl

theorem cell23_5288747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 3, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 3, 6, 1, 4].length) (baseStart_5288747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5288747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5288747 prefixEnd_5288747 := by exact prefixLift 5288747
  have htrace : WordTrace (prefixWord ++ tailWord_5288747) baseStart_5288747 baseEnd_5288747 := by
    simpa [prefixWord, tailWord_5288747, baseEnd_5288747] using wordTrace_append hprefix tailTrace_5288747
  have hstable : (prefixWord ++ tailWord_5288747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5288747).length < 2 ^ (prefixWord ++ tailWord_5288747).sum := by decide
  have hdescent : baseEnd_5288747 < baseStart_5288747 := by decide
  rcases family_descends (prefixWord ++ tailWord_5288747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5288764 : List Nat := [2, 2, 2, 2, 1, 1, 1, 1, 3, 6, 2]
def baseStart_5288764 : Nat := 118140960795 + 5288764 * 2 ^ 59
def prefixEnd_5288764 : Nat := 4983230072969 + 3 ^ 40 * 5288764 * 2
def baseEnd_5288764 : Nat := 2715678000195450920227423

theorem tailTrace_5288764 : CollatzResearch.WordTrace tailWord_5288764 prefixEnd_5288764 2715678000195450920227423 := by
  unfold tailWord_5288764
  simp only [CollatzResearch.WordTrace]
  refine ⟨96448535105859375912492673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128598046807812501216656897 96448535105859375912492673)
  ·
    refine ⟨72336401329394531934369505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96448535105859375912492673 72336401329394531934369505)
    ·
      refine ⟨54252300997045898950777129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72336401329394531934369505 54252300997045898950777129)
      ·
        refine ⟨40689225747784424213082847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54252300997045898950777129 40689225747784424213082847)
        ·
          refine ⟨61033838621676636319624271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40689225747784424213082847 61033838621676636319624271)
          ·
            refine ⟨91550757932514954479436407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61033838621676636319624271 91550757932514954479436407)
            ·
              refine ⟨137326136898772431719154611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91550757932514954479436407 137326136898772431719154611)
              ·
                refine ⟨205989205348158647578731917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 137326136898772431719154611 205989205348158647578731917)
                ·
                  refine ⟨77245952005559492842024469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 205989205348158647578731917 77245952005559492842024469)
                  ·
                    refine ⟨3620904000260601226969897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 77245952005559492842024469 3620904000260601226969897)
                    ·
                      refine ⟨2715678000195450920227423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3620904000260601226969897 2715678000195450920227423)
                      ·
                        rfl

theorem cell23_5288764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 1, 3, 6, 2].length) (baseStart_5288764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5288764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5288764 prefixEnd_5288764 := by exact prefixLift 5288764
  have htrace : WordTrace (prefixWord ++ tailWord_5288764) baseStart_5288764 baseEnd_5288764 := by
    simpa [prefixWord, tailWord_5288764, baseEnd_5288764] using wordTrace_append hprefix tailTrace_5288764
  have hstable : (prefixWord ++ tailWord_5288764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5288764).length < 2 ^ (prefixWord ++ tailWord_5288764).sum := by decide
  have hdescent : baseEnd_5288764 < baseStart_5288764 := by decide
  rcases family_descends (prefixWord ++ tailWord_5288764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5288777 : List Nat := [1, 2, 1, 1, 2, 5, 1, 1, 2, 1, 6]
def baseStart_5288777 : Nat := 118140960795 + 5288777 * 2 ^ 59
def prefixEnd_5288777 : Nat := 4983230072969 + 3 ^ 40 * 5288777 * 2
def baseEnd_5288777 : Nat := 2715684675443959369364863

theorem tailTrace_5288777 : CollatzResearch.WordTrace tailWord_5288777 prefixEnd_5288777 2715684675443959369364863 := by
  unfold tailWord_5288777
  simp only [CollatzResearch.WordTrace]
  refine ⟨192897544360671655045208585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128598362907114436696805723 192897544360671655045208585)
  ·
    refine ⟨144673158270503741283906439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192897544360671655045208585 144673158270503741283906439)
    ·
      refine ⟨217009737405755611925859659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144673158270503741283906439 217009737405755611925859659)
      ·
        refine ⟨325514606108633417888789489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 217009737405755611925859659 325514606108633417888789489)
        ·
          refine ⟨244135954581475063416592117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 325514606108633417888789489 244135954581475063416592117)
          ·
            refine ⟨22887745742013287195305511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 244135954581475063416592117 22887745742013287195305511)
            ·
              refine ⟨34331618613019930792958267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22887745742013287195305511 34331618613019930792958267)
              ·
                refine ⟨51497427919529896189437401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34331618613019930792958267 51497427919529896189437401)
                ·
                  refine ⟨38623070939647422142078051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51497427919529896189437401 38623070939647422142078051)
                  ·
                    refine ⟨57934606409471133213117077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 38623070939647422142078051 57934606409471133213117077)
                    ·
                      refine ⟨2715684675443959369364863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 57934606409471133213117077 2715684675443959369364863)
                      ·
                        rfl

theorem cell23_5288777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 1, 2, 1, 6].length) (baseStart_5288777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5288777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5288777 prefixEnd_5288777 := by exact prefixLift 5288777
  have htrace : WordTrace (prefixWord ++ tailWord_5288777) baseStart_5288777 baseEnd_5288777 := by
    simpa [prefixWord, tailWord_5288777, baseEnd_5288777] using wordTrace_append hprefix tailTrace_5288777
  have hstable : (prefixWord ++ tailWord_5288777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5288777).length < 2 ^ (prefixWord ++ tailWord_5288777).sum := by decide
  have hdescent : baseEnd_5288777 < baseStart_5288777 := by decide
  rcases family_descends (prefixWord ++ tailWord_5288777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5288784 : List Nat := [2, 1, 1, 1, 1, 4, 2, 4, 2, 2, 3]
def baseStart_5288784 : Nat := 118140960795 + 5288784 * 2 ^ 59
def prefixEnd_5288784 : Nat := 4983230072969 + 3 ^ 40 * 5288784 * 2
def baseEnd_5288784 : Nat := 2715688269808540841977331

theorem tailTrace_5288784 : CollatzResearch.WordTrace tailWord_5288784 prefixEnd_5288784 2715688269808540841977331 := by
  unfold tailWord_5288784
  simp only [CollatzResearch.WordTrace]
  refine ⟨96448899835823147620356703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128598533114430863493808937 96448899835823147620356703)
  ·
    refine ⟨144673349753734721430535055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96448899835823147620356703 144673349753734721430535055)
    ·
      refine ⟨217010024630602082145802583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144673349753734721430535055 217010024630602082145802583)
      ·
        refine ⟨325515036945903123218703875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 217010024630602082145802583 325515036945903123218703875)
        ·
          refine ⟨488272555418854684828055813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 325515036945903123218703875 488272555418854684828055813)
          ·
            refine ⟨91551104141035253405260465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 488272555418854684828055813 91551104141035253405260465)
            ·
              refine ⟨68663328105776440053945349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91551104141035253405260465 68663328105776440053945349)
              ·
                refine ⟨12874374019833082510114753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 68663328105776440053945349 12874374019833082510114753)
                ·
                  refine ⟨9655780514874811882586065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12874374019833082510114753 9655780514874811882586065)
                  ·
                    refine ⟨7241835386156108911939549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9655780514874811882586065 7241835386156108911939549)
                    ·
                      refine ⟨2715688269808540841977331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7241835386156108911939549 2715688269808540841977331)
                      ·
                        rfl

theorem cell23_5288784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 4, 2, 2, 3].length) (baseStart_5288784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5288784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5288784 prefixEnd_5288784 := by exact prefixLift 5288784
  have htrace : WordTrace (prefixWord ++ tailWord_5288784) baseStart_5288784 baseEnd_5288784 := by
    simpa [prefixWord, tailWord_5288784, baseEnd_5288784] using wordTrace_append hprefix tailTrace_5288784
  have hstable : (prefixWord ++ tailWord_5288784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5288784).length < 2 ^ (prefixWord ++ tailWord_5288784).sum := by decide
  have hdescent : baseEnd_5288784 < baseStart_5288784 := by decide
  rcases family_descends (prefixWord ++ tailWord_5288784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5288791 : List Nat := [1, 1, 3, 2, 4, 2, 2, 1, 3, 4]
def baseStart_5288791 : Nat := 118140960795 + 5288791 * 2 ^ 59
def prefixEnd_5288791 : Nat := 4983230072969 + 3 ^ 40 * 5288791 * 2
def baseEnd_5288791 : Nat := 905230621391040771529933

theorem tailTrace_5288791 : CollatzResearch.WordTrace tailWord_5288791 prefixEnd_5288791 905230621391040771529933 := by
  unfold tailWord_5288791
  simp only [CollatzResearch.WordTrace]
  refine ⟨192898054982620935436218227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128598703321747290290812151 192898054982620935436218227)
  ·
    refine ⟨289347082473931403154327341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192898054982620935436218227 289347082473931403154327341)
    ·
      refine ⟨108505155927724276182872753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 289347082473931403154327341 108505155927724276182872753)
      ·
        refine ⟨81378866945793207137154565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108505155927724276182872753 81378866945793207137154565)
        ·
          refine ⟨15258537552336226338216481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 81378866945793207137154565 15258537552336226338216481)
          ·
            refine ⟨11443903164252169753662361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15258537552336226338216481 11443903164252169753662361)
            ·
              refine ⟨8582927373189127315246771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11443903164252169753662361 8582927373189127315246771)
              ·
                refine ⟨12874391059783690972870157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8582927373189127315246771 12874391059783690972870157)
                ·
                  refine ⟨4827896647418884114826309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12874391059783690972870157 4827896647418884114826309)
                  ·
                    refine ⟨905230621391040771529933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4827896647418884114826309 905230621391040771529933)
                    ·
                      rfl

theorem cell23_5288791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 2, 1, 3, 4].length) (baseStart_5288791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5288791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5288791 prefixEnd_5288791 := by exact prefixLift 5288791
  have htrace : WordTrace (prefixWord ++ tailWord_5288791) baseStart_5288791 baseEnd_5288791 := by
    simpa [prefixWord, tailWord_5288791, baseEnd_5288791] using wordTrace_append hprefix tailTrace_5288791
  have hstable : (prefixWord ++ tailWord_5288791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5288791).length < 2 ^ (prefixWord ++ tailWord_5288791).sum := by decide
  have hdescent : baseEnd_5288791 < baseStart_5288791 := by decide
  rcases family_descends (prefixWord ++ tailWord_5288791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5288841 : List Nat := [1, 2, 1, 1, 5, 2, 1, 1, 4, 3, 2]
def baseStart_5288841 : Nat := 118140960795 + 5288841 * 2 ^ 59
def prefixEnd_5288841 : Nat := 4983230072969 + 3 ^ 40 * 5288841 * 2
def baseEnd_5288841 : Nat := 2715717538205847118964569

theorem tailTrace_5288841 : CollatzResearch.WordTrace tailWord_5288841 prefixEnd_5288841 2715717538205847118964569 := by
  unfold tailWord_5288841
  simp only [CollatzResearch.WordTrace]
  refine ⟨192899878632439793975538377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128599919088293195983692251 192899878632439793975538377)
  ·
    refine ⟨144674908974329845481653783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192899878632439793975538377 144674908974329845481653783)
    ·
      refine ⟨217012363461494768222480675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144674908974329845481653783 217012363461494768222480675)
      ·
        refine ⟨325518545192242152333721013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 217012363461494768222480675 325518545192242152333721013)
        ·
          refine ⟨30517363611772701781286345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 325518545192242152333721013 30517363611772701781286345)
          ·
            refine ⟨22888022708829526335964759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30517363611772701781286345 22888022708829526335964759)
            ·
              refine ⟨34332034063244289503947139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22888022708829526335964759 34332034063244289503947139)
              ·
                refine ⟨51498051094866434255920709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34332034063244289503947139 51498051094866434255920709)
                ·
                  refine ⟨9655884580287456422985133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 51498051094866434255920709 9655884580287456422985133)
                  ·
                    refine ⟨3620956717607796158619425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9655884580287456422985133 3620956717607796158619425)
                    ·
                      refine ⟨2715717538205847118964569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3620956717607796158619425 2715717538205847118964569)
                      ·
                        rfl

theorem cell23_5288841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 1, 4, 3, 2].length) (baseStart_5288841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5288841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5288841 prefixEnd_5288841 := by exact prefixLift 5288841
  have htrace : WordTrace (prefixWord ++ tailWord_5288841) baseStart_5288841 baseEnd_5288841 := by
    simpa [prefixWord, tailWord_5288841, baseEnd_5288841] using wordTrace_append hprefix tailTrace_5288841
  have hstable : (prefixWord ++ tailWord_5288841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5288841).length < 2 ^ (prefixWord ++ tailWord_5288841).sum := by decide
  have hdescent : baseEnd_5288841 < baseStart_5288841 := by decide
  rcases family_descends (prefixWord ++ tailWord_5288841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5288881 : List Nat := [1, 2, 2, 4, 3, 1, 1, 2, 1, 6]
def baseStart_5288881 : Nat := 118140960795 + 5288881 * 2 ^ 59
def prefixEnd_5288881 : Nat := 4983230072969 + 3 ^ 40 * 5288881 * 2
def baseEnd_5288881 : Nat := 905246025810675654154795

theorem tailTrace_5288881 : CollatzResearch.WordTrace tailWord_5288881 prefixEnd_5288881 905246025810675654154795 := by
  unfold tailWord_5288881
  simp only [CollatzResearch.WordTrace]
  refine ⟨192901337552294880806994497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128600891701529920537996331 192901337552294880806994497)
  ·
    refine ⟨144676003164221160605245873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192901337552294880806994497 144676003164221160605245873)
    ·
      refine ⟨108507002373165870453934405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144676003164221160605245873 108507002373165870453934405)
      ·
        refine ⟨20345062944968600710112701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 108507002373165870453934405 20345062944968600710112701)
        ·
          refine ⟨7629398604363225266292263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20345062944968600710112701 7629398604363225266292263)
          ·
            refine ⟨11444097906544837899438395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7629398604363225266292263 11444097906544837899438395)
            ·
              refine ⟨17166146859817256849157593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11444097906544837899438395 17166146859817256849157593)
              ·
                refine ⟨12874610144862942636868195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17166146859817256849157593 12874610144862942636868195)
                ·
                  refine ⟨19311915217294413955302293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12874610144862942636868195 19311915217294413955302293)
                  ·
                    refine ⟨905246025810675654154795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19311915217294413955302293 905246025810675654154795)
                    ·
                      rfl

theorem cell23_5288881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 1, 2, 1, 6].length) (baseStart_5288881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5288881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5288881 prefixEnd_5288881 := by exact prefixLift 5288881
  have htrace : WordTrace (prefixWord ++ tailWord_5288881) baseStart_5288881 baseEnd_5288881 := by
    simpa [prefixWord, tailWord_5288881, baseEnd_5288881] using wordTrace_append hprefix tailTrace_5288881
  have hstable : (prefixWord ++ tailWord_5288881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5288881).length < 2 ^ (prefixWord ++ tailWord_5288881).sum := by decide
  have hdescent : baseEnd_5288881 < baseStart_5288881 := by decide
  rcases family_descends (prefixWord ++ tailWord_5288881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5288888 : List Nat := [2, 1, 2, 1, 2, 5, 3, 1, 1, 1, 4]
def baseStart_5288888 : Nat := 118140960795 + 5288888 * 2 ^ 59
def prefixEnd_5288888 : Nat := 4983230072969 + 3 ^ 40 * 5288888 * 2
def baseEnd_5288888 : Nat := 2715741671796608435076853

theorem tailTrace_5288888 : CollatzResearch.WordTrace tailWord_5288888 prefixEnd_5288888 2715741671796608435076853 := by
  unfold tailWord_5288888
  simp only [CollatzResearch.WordTrace]
  refine ⟨96450796431634760501249659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128601061908846347334999545 96450796431634760501249659)
  ·
    refine ⟨144676194647452140751874489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96450796431634760501249659 144676194647452140751874489)
    ·
      refine ⟨108507145985589105563905867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144676194647452140751874489 108507145985589105563905867)
      ·
        refine ⟨162760718978383658345858801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108507145985589105563905867 162760718978383658345858801)
        ·
          refine ⟨122070539233787743759394101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 162760718978383658345858801 122070539233787743759394101)
          ·
            refine ⟨11444113053167600977443197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 122070539233787743759394101 11444113053167600977443197)
            ·
              refine ⟨4291542394937850366541199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11444113053167600977443197 4291542394937850366541199)
              ·
                refine ⟨6437313592406775549811799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4291542394937850366541199 6437313592406775549811799)
                ·
                  refine ⟨9655970388610163324717699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6437313592406775549811799 9655970388610163324717699)
                  ·
                    refine ⟨14483955582915244987076549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9655970388610163324717699 14483955582915244987076549)
                    ·
                      refine ⟨2715741671796608435076853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14483955582915244987076549 2715741671796608435076853)
                      ·
                        rfl

theorem cell23_5288888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 3, 1, 1, 1, 4].length) (baseStart_5288888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5288888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5288888 prefixEnd_5288888 := by exact prefixLift 5288888
  have htrace : WordTrace (prefixWord ++ tailWord_5288888) baseStart_5288888 baseEnd_5288888 := by
    simpa [prefixWord, tailWord_5288888, baseEnd_5288888] using wordTrace_append hprefix tailTrace_5288888
  have hstable : (prefixWord ++ tailWord_5288888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5288888).length < 2 ^ (prefixWord ++ tailWord_5288888).sum := by decide
  have hdescent : baseEnd_5288888 < baseStart_5288888 := by decide
  rcases family_descends (prefixWord ++ tailWord_5288888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5288918 : List Nat := [5, 2, 1, 1, 2, 1, 1, 3, 1, 2, 4]
def baseStart_5288918 : Nat := 118140960795 + 5288918 * 2 ^ 59
def prefixEnd_5288918 : Nat := 4983230072969 + 3 ^ 40 * 5288918 * 2
def baseEnd_5288918 : Nat := 2715757076216243317701715

theorem tailTrace_5288918 : CollatzResearch.WordTrace tailWord_5288918 prefixEnd_5288918 2715757076216243317701715 := by
  unfold tailWord_5288918
  simp only [CollatzResearch.WordTrace]
  refine ⟨12056417940822552257880713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 128601791368773890750727605 12056417940822552257880713)
  ·
    refine ⟨9042313455616914193410535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12056417940822552257880713 9042313455616914193410535)
    ·
      refine ⟨13563470183425371290115803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9042313455616914193410535 13563470183425371290115803)
      ·
        refine ⟨20345205275138056935173705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13563470183425371290115803 20345205275138056935173705)
        ·
          refine ⟨15258903956353542701380279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20345205275138056935173705 15258903956353542701380279)
          ·
            refine ⟨22888355934530314052070419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15258903956353542701380279 22888355934530314052070419)
            ·
              refine ⟨34332533901795471078105629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22888355934530314052070419 34332533901795471078105629)
              ·
                refine ⟨12874700213173301654289611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34332533901795471078105629 12874700213173301654289611)
                ·
                  refine ⟨19312050319759952481434417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12874700213173301654289611 19312050319759952481434417)
                  ·
                    refine ⟨14484037739819964361075813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19312050319759952481434417 14484037739819964361075813)
                    ·
                      refine ⟨2715757076216243317701715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14484037739819964361075813 2715757076216243317701715)
                      ·
                        rfl

theorem cell23_5288918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 3, 1, 2, 4].length) (baseStart_5288918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5288918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5288918 prefixEnd_5288918 := by exact prefixLift 5288918
  have htrace : WordTrace (prefixWord ++ tailWord_5288918) baseStart_5288918 baseEnd_5288918 := by
    simpa [prefixWord, tailWord_5288918, baseEnd_5288918] using wordTrace_append hprefix tailTrace_5288918
  have hstable : (prefixWord ++ tailWord_5288918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5288918).length < 2 ^ (prefixWord ++ tailWord_5288918).sum := by decide
  have hdescent : baseEnd_5288918 < baseStart_5288918 := by decide
  rcases family_descends (prefixWord ++ tailWord_5288918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5288921 : List Nat := [1, 2, 1, 2, 5, 1, 1, 3, 1, 3, 3]
def baseStart_5288921 : Nat := 118140960795 + 5288921 * 2 ^ 59
def prefixEnd_5288921 : Nat := 4983230072969 + 3 ^ 40 * 5288921 * 2
def baseEnd_5288921 : Nat := 2715758616658206805964201

theorem tailTrace_5288921 : CollatzResearch.WordTrace tailWord_5288921 prefixEnd_5288921 2715758616658206805964201 := by
  unfold tailWord_5288921
  simp only [CollatzResearch.WordTrace]
  refine ⟨192902796472149967638450617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128601864314766645092300411 192902796472149967638450617)
  ·
    refine ⟨144677097354112475728837963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192902796472149967638450617 144677097354112475728837963)
    ·
      refine ⟨217015646031168713593256945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144677097354112475728837963 217015646031168713593256945)
      ·
        refine ⟨162761734523376535194942709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 217015646031168713593256945 162761734523376535194942709)
        ·
          refine ⟨15258912611566550174525879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 162761734523376535194942709 15258912611566550174525879)
          ·
            refine ⟨22888368917349825261788819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15258912611566550174525879 22888368917349825261788819)
            ·
              refine ⟨34332553376024737892683229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22888368917349825261788819 34332553376024737892683229)
              ·
                refine ⟨12874707516009276709756211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34332553376024737892683229 12874707516009276709756211)
                ·
                  refine ⟨19312061274013915064634317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12874707516009276709756211 19312061274013915064634317)
                  ·
                    refine ⟨7242022977755218149237869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19312061274013915064634317 7242022977755218149237869)
                    ·
                      refine ⟨2715758616658206805964201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7242022977755218149237869 2715758616658206805964201)
                      ·
                        rfl

theorem cell23_5288921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 3, 1, 3, 3].length) (baseStart_5288921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5288921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5288921 prefixEnd_5288921 := by exact prefixLift 5288921
  have htrace : WordTrace (prefixWord ++ tailWord_5288921) baseStart_5288921 baseEnd_5288921 := by
    simpa [prefixWord, tailWord_5288921, baseEnd_5288921] using wordTrace_append hprefix tailTrace_5288921
  have hstable : (prefixWord ++ tailWord_5288921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5288921).length < 2 ^ (prefixWord ++ tailWord_5288921).sum := by decide
  have hdescent : baseEnd_5288921 < baseStart_5288921 := by decide
  rcases family_descends (prefixWord ++ tailWord_5288921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5288942 : List Nat := [4, 1, 2, 1, 4, 2, 2, 1, 1, 2, 3]
def baseStart_5288942 : Nat := 118140960795 + 5288942 * 2 ^ 59
def prefixEnd_5288942 : Nat := 4983230072969 + 3 ^ 40 * 5288942 * 2
def baseEnd_5288942 : Nat := 2715769399751951223801605

theorem tailTrace_5288942 : CollatzResearch.WordTrace tailWord_5288942 prefixEnd_5288942 2715769399751951223801605 := by
  unfold tailWord_5288942
  simp only [CollatzResearch.WordTrace]
  refine ⟨24112945300634236028120635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 128602374936715925483310053 24112945300634236028120635)
  ·
    refine ⟨36169417950951354042180953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24112945300634236028120635 36169417950951354042180953)
    ·
      refine ⟨27127063463213515531635715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36169417950951354042180953 27127063463213515531635715)
      ·
        refine ⟨40690595194820273297453573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27127063463213515531635715 40690595194820273297453573)
        ·
          refine ⟨7629486599028801243272545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40690595194820273297453573 7629486599028801243272545)
          ·
            refine ⟨5722114949271600932454409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7629486599028801243272545 5722114949271600932454409)
            ·
              refine ⟨4291586211953700699340807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5722114949271600932454409 4291586211953700699340807)
              ·
                refine ⟨6437379317930551049011211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4291586211953700699340807 6437379317930551049011211)
                ·
                  refine ⟨9656068976895826573516817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6437379317930551049011211 9656068976895826573516817)
                  ·
                    refine ⟨7242051732671869930137613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9656068976895826573516817 7242051732671869930137613)
                    ·
                      refine ⟨2715769399751951223801605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7242051732671869930137613 2715769399751951223801605)
                      ·
                        rfl

theorem cell23_5288942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 2, 1, 1, 2, 3].length) (baseStart_5288942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5288942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5288942 prefixEnd_5288942 := by exact prefixLift 5288942
  have htrace : WordTrace (prefixWord ++ tailWord_5288942) baseStart_5288942 baseEnd_5288942 := by
    simpa [prefixWord, tailWord_5288942, baseEnd_5288942] using wordTrace_append hprefix tailTrace_5288942
  have hstable : (prefixWord ++ tailWord_5288942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5288942).length < 2 ^ (prefixWord ++ tailWord_5288942).sum := by decide
  have hdescent : baseEnd_5288942 < baseStart_5288942 := by decide
  rcases family_descends (prefixWord ++ tailWord_5288942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5288949 : List Nat := [1, 3, 5, 2, 2, 1, 1, 2, 2, 4]
def baseStart_5288949 : Nat := 118140960795 + 5288949 * 2 ^ 59
def prefixEnd_5288949 : Nat := 4983230072969 + 3 ^ 40 * 5288949 * 2
def baseEnd_5288949 : Nat := 905257664705510898804691

theorem tailTrace_5288949 : CollatzResearch.WordTrace tailWord_5288949 prefixEnd_5288949 905257664705510898804691 := by
  unfold tailWord_5288949
  simp only [CollatzResearch.WordTrace]
  refine ⟨192903817716048528420469901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128602545144032352280313267 192903817716048528420469901)
  ·
    refine ⟨72338931643518198157676213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 192903817716048528420469901 72338931643518198157676213)
    ·
      refine ⟨6781774841579831077282145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 72338931643518198157676213 6781774841579831077282145)
      ·
        refine ⟨5086331131184873307961609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6781774841579831077282145 5086331131184873307961609)
        ·
          refine ⟨3814748348388654980971207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5086331131184873307961609 3814748348388654980971207)
          ·
            refine ⟨5722122522582982471456811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3814748348388654980971207 5722122522582982471456811)
            ·
              refine ⟨8583183783874473707185217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5722122522582982471456811 8583183783874473707185217)
              ·
                refine ⟨6437387837905855280388913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8583183783874473707185217 6437387837905855280388913)
                ·
                  refine ⟨4828040878429391460291685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6437387837905855280388913 4828040878429391460291685)
                  ·
                    refine ⟨905257664705510898804691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4828040878429391460291685 905257664705510898804691)
                    ·
                      rfl

theorem cell23_5288949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 1, 2, 2, 4].length) (baseStart_5288949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5288949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5288949 prefixEnd_5288949 := by exact prefixLift 5288949
  have htrace : WordTrace (prefixWord ++ tailWord_5288949) baseStart_5288949 baseEnd_5288949 := by
    simpa [prefixWord, tailWord_5288949, baseEnd_5288949] using wordTrace_append hprefix tailTrace_5288949
  have hstable : (prefixWord ++ tailWord_5288949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5288949).length < 2 ^ (prefixWord ++ tailWord_5288949).sum := by decide
  have hdescent : baseEnd_5288949 < baseStart_5288949 := by decide
  rcases family_descends (prefixWord ++ tailWord_5288949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5289012 : List Nat := [2, 5, 1, 2, 1, 1, 2, 1, 4, 2, 2]
def baseStart_5289012 : Nat := 118140960795 + 5289012 * 2 ^ 59
def prefixEnd_5289012 : Nat := 4983230072969 + 3 ^ 40 * 5289012 * 2
def baseEnd_5289012 : Nat := 2715805343397765949926283

theorem tailTrace_5289012 : CollatzResearch.WordTrace tailWord_5289012 prefixEnd_5289012 2715805343397765949926283 := by
  unfold tailWord_5289012
  simp only [CollatzResearch.WordTrace]
  refine ⟨96453057757410145090006645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128604077009880193453342193 96453057757410145090006645)
  ·
    refine ⟨9042474164757201102188123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 96453057757410145090006645 9042474164757201102188123)
    ·
      refine ⟨13563711247135801653282185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9042474164757201102188123 13563711247135801653282185)
      ·
        refine ⟨10172783435351851239961639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13563711247135801653282185 10172783435351851239961639)
        ·
          refine ⟨15259175153027776859942459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10172783435351851239961639 15259175153027776859942459)
          ·
            refine ⟨22888762729541665289913689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15259175153027776859942459 22888762729541665289913689)
            ·
              refine ⟨17166572047156248967435267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22888762729541665289913689 17166572047156248967435267)
              ·
                refine ⟨25749858070734373451152901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17166572047156248967435267 25749858070734373451152901)
                ·
                  refine ⟨4828098388262695022091169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25749858070734373451152901 4828098388262695022091169)
                  ·
                    refine ⟨3621073791197021266568377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4828098388262695022091169 3621073791197021266568377)
                    ·
                      refine ⟨2715805343397765949926283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3621073791197021266568377 2715805343397765949926283)
                      ·
                        rfl

theorem cell23_5289012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 2, 1, 4, 2, 2].length) (baseStart_5289012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5289012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5289012 prefixEnd_5289012 := by exact prefixLift 5289012
  have htrace : WordTrace (prefixWord ++ tailWord_5289012) baseStart_5289012 baseEnd_5289012 := by
    simpa [prefixWord, tailWord_5289012, baseEnd_5289012] using wordTrace_append hprefix tailTrace_5289012
  have hstable : (prefixWord ++ tailWord_5289012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5289012).length < 2 ^ (prefixWord ++ tailWord_5289012).sum := by decide
  have hdescent : baseEnd_5289012 < baseStart_5289012 := by decide
  rcases family_descends (prefixWord ++ tailWord_5289012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5289058 : List Nat := [3, 3, 2, 2, 1, 1, 1, 2, 1, 2, 5]
def baseStart_5289058 : Nat := 118140960795 + 5289058 * 2 ^ 59
def prefixEnd_5289058 : Nat := 4983230072969 + 3 ^ 40 * 5289058 * 2
def baseEnd_5289058 : Nat := 2715828963507872769951071

theorem tailTrace_5289058 : CollatzResearch.WordTrace tailWord_5289058 prefixEnd_5289058 2715828963507872769951071 := by
  unfold tailWord_5289058
  simp only [CollatzResearch.WordTrace]
  refine ⟨48226948318163410009046957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128605195515102426690791885 48226948318163410009046957)
  ·
    refine ⟨18085105619311278753392609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48226948318163410009046957 18085105619311278753392609)
    ·
      refine ⟨13563829214483459065044457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18085105619311278753392609 13563829214483459065044457)
      ·
        refine ⟨10172871910862594298783343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13563829214483459065044457 10172871910862594298783343)
        ·
          refine ⟨15259307866293891448175015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10172871910862594298783343 15259307866293891448175015)
          ·
            refine ⟨22888961799440837172262523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15259307866293891448175015 22888961799440837172262523)
            ·
              refine ⟨34333442699161255758393785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22888961799440837172262523 34333442699161255758393785)
              ·
                refine ⟨25750082024370941818795339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34333442699161255758393785 25750082024370941818795339)
                ·
                  refine ⟨38625123036556412728193009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25750082024370941818795339 38625123036556412728193009)
                  ·
                    refine ⟨28968842277417309546144757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 38625123036556412728193009 28968842277417309546144757)
                    ·
                      refine ⟨2715828963507872769951071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28968842277417309546144757 2715828963507872769951071)
                      ·
                        rfl

theorem cell23_5289058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 2, 1, 2, 5].length) (baseStart_5289058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5289058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5289058 prefixEnd_5289058 := by exact prefixLift 5289058
  have htrace : WordTrace (prefixWord ++ tailWord_5289058) baseStart_5289058 baseEnd_5289058 := by
    simpa [prefixWord, tailWord_5289058, baseEnd_5289058] using wordTrace_append hprefix tailTrace_5289058
  have hstable : (prefixWord ++ tailWord_5289058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5289058).length < 2 ^ (prefixWord ++ tailWord_5289058).sum := by decide
  have hdescent : baseEnd_5289058 < baseStart_5289058 := by decide
  rcases family_descends (prefixWord ++ tailWord_5289058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5289068 : List Nat := [2, 2, 1, 1, 3, 2, 2, 2, 2, 4, 2]
def baseStart_5289068 : Nat := 118140960795 + 5289068 * 2 ^ 59
def prefixEnd_5289068 : Nat := 4983230072969 + 3 ^ 40 * 5289068 * 2
def baseEnd_5289068 : Nat := 2715834098314417730826025

theorem tailTrace_5289068 : CollatzResearch.WordTrace tailWord_5289068 prefixEnd_5289068 2715834098314417730826025 := by
  unfold tailWord_5289068
  simp only [CollatzResearch.WordTrace]
  refine ⟨96454079001308705872025929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128605438668411607829367905 96454079001308705872025929)
  ·
    refine ⟨72340559250981529404019447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96454079001308705872025929 72340559250981529404019447)
    ·
      refine ⟨108510838876472294106029171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72340559250981529404019447 108510838876472294106029171)
      ·
        refine ⟨162766258314708441159043757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108510838876472294106029171 162766258314708441159043757)
        ·
          refine ⟨61037346868015665434641409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 162766258314708441159043757 61037346868015665434641409)
          ·
            refine ⟨45778010151011749075981057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61037346868015665434641409 45778010151011749075981057)
            ·
              refine ⟨34333507613258811806985793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45778010151011749075981057 34333507613258811806985793)
              ·
                refine ⟨25750130709944108855239345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34333507613258811806985793 25750130709944108855239345)
                ·
                  refine ⟨19312598032458081641429509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25750130709944108855239345 19312598032458081641429509)
                  ·
                    refine ⟨3621112131085890307768033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19312598032458081641429509 3621112131085890307768033)
                    ·
                      refine ⟨2715834098314417730826025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3621112131085890307768033 2715834098314417730826025)
                      ·
                        rfl

theorem cell23_5289068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 4, 2].length) (baseStart_5289068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5289068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5289068 prefixEnd_5289068 := by exact prefixLift 5289068
  have htrace : WordTrace (prefixWord ++ tailWord_5289068) baseStart_5289068 baseEnd_5289068 := by
    simpa [prefixWord, tailWord_5289068, baseEnd_5289068] using wordTrace_append hprefix tailTrace_5289068
  have hstable : (prefixWord ++ tailWord_5289068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5289068).length < 2 ^ (prefixWord ++ tailWord_5289068).sum := by decide
  have hdescent : baseEnd_5289068 < baseStart_5289068 := by decide
  rcases family_descends (prefixWord ++ tailWord_5289068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5289091 : List Nat := [1, 1, 1, 3, 3, 2, 1, 5, 6]
def baseStart_5289091 : Nat := 118140960795 + 5289091 * 2 ^ 59
def prefixEnd_5289091 : Nat := 4983230072969 + 3 ^ 40 * 5289091 * 2
def baseEnd_5289091 : Nat := 301760656485496793426491

theorem tailTrace_5289091 : CollatzResearch.WordTrace tailWord_5289091 prefixEnd_5289091 301760656485496793426491 := by
  unfold tailWord_5289091
  simp only [CollatzResearch.WordTrace]
  refine ⟨192908996881534086672139127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128605997921022724448092751 192908996881534086672139127)
  ·
    refine ⟨289363495322301130008208691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192908996881534086672139127 289363495322301130008208691)
    ·
      refine ⟨434045242983451695012313037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 289363495322301130008208691 434045242983451695012313037)
      ·
        refine ⟨162766966118794385629617389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 434045242983451695012313037 162766966118794385629617389)
        ·
          refine ⟨61037612294547894611106521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 162766966118794385629617389 61037612294547894611106521)
          ·
            refine ⟨45778209220910920958329891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61037612294547894611106521 45778209220910920958329891)
            ·
              refine ⟨68667313831366381437494837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45778209220910920958329891 68667313831366381437494837)
              ·
                refine ⟨6437560671690598259765141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 68667313831366381437494837 6437560671690598259765141)
                ·
                  refine ⟨301760656485496793426491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6437560671690598259765141 301760656485496793426491)
                  ·
                    rfl

theorem cell23_5289091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 5, 6].length) (baseStart_5289091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5289091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5289091 prefixEnd_5289091 := by exact prefixLift 5289091
  have htrace : WordTrace (prefixWord ++ tailWord_5289091) baseStart_5289091 baseEnd_5289091 := by
    simpa [prefixWord, tailWord_5289091, baseEnd_5289091] using wordTrace_append hprefix tailTrace_5289091
  have hstable : (prefixWord ++ tailWord_5289091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5289091).length < 2 ^ (prefixWord ++ tailWord_5289091).sum := by decide
  have hdescent : baseEnd_5289091 < baseStart_5289091 := by decide
  rcases family_descends (prefixWord ++ tailWord_5289091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5289112 : List Nat := [2, 1, 2, 4, 2, 2, 2, 3, 1, 4]
def baseStart_5289112 : Nat := 118140960795 + 5289112 * 2 ^ 59
def prefixEnd_5289112 : Nat := 4983230072969 + 3 ^ 40 * 5289112 * 2
def baseEnd_5289112 : Nat := 905285563821071852891941

theorem tailTrace_5289112 : CollatzResearch.WordTrace tailWord_5289112 prefixEnd_5289112 905285563821071852891941 := by
  unfold tailWord_5289112
  simp only [CollatzResearch.WordTrace]
  refine ⟨96454881407229003629326795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128606508542972004839102393 96454881407229003629326795)
  ·
    refine ⟨144682322110843505443990193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96454881407229003629326795 144682322110843505443990193)
    ·
      refine ⟨108511741583132629082992645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144682322110843505443990193 108511741583132629082992645)
      ·
        refine ⟨20345951546837367953061121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 108511741583132629082992645 20345951546837367953061121)
        ·
          refine ⟨15259463660128025964795841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20345951546837367953061121 15259463660128025964795841)
          ·
            refine ⟨11444597745096019473596881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15259463660128025964795841 11444597745096019473596881)
            ·
              refine ⟨8583448308822014605197661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11444597745096019473596881 8583448308822014605197661)
              ·
                refine ⟨3218793115808255476949123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8583448308822014605197661 3218793115808255476949123)
                ·
                  refine ⟨4828189673712383215423685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3218793115808255476949123 4828189673712383215423685)
                  ·
                    refine ⟨905285563821071852891941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4828189673712383215423685 905285563821071852891941)
                    ·
                      rfl

theorem cell23_5289112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 2, 3, 1, 4].length) (baseStart_5289112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5289112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5289112 prefixEnd_5289112 := by exact prefixLift 5289112
  have htrace : WordTrace (prefixWord ++ tailWord_5289112) baseStart_5289112 baseEnd_5289112 := by
    simpa [prefixWord, tailWord_5289112, baseEnd_5289112] using wordTrace_append hprefix tailTrace_5289112
  have hstable : (prefixWord ++ tailWord_5289112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5289112).length < 2 ^ (prefixWord ++ tailWord_5289112).sum := by decide
  have hdescent : baseEnd_5289112 < baseStart_5289112 := by decide
  rcases family_descends (prefixWord ++ tailWord_5289112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5289175 : List Nat := [1, 1, 3, 2, 1, 2, 2, 2, 5, 2, 2]
def baseStart_5289175 : Nat := 118140960795 + 5289175 * 2 ^ 59
def prefixEnd_5289175 : Nat := 4983230072969 + 3 ^ 40 * 5289175 * 2
def baseEnd_5289175 : Nat := 2715889040744448812188033

theorem tailTrace_5289175 : CollatzResearch.WordTrace tailWord_5289175 prefixEnd_5289175 2715889040744448812188033 := by
  unfold tailWord_5289175
  simp only [CollatzResearch.WordTrace]
  refine ⟨192912060613229769018196979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128608040408819846012131319 192912060613229769018196979)
  ·
    refine ⟨289368090919844653527295469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192912060613229769018196979 289368090919844653527295469)
    ·
      refine ⟨108513034094941745072735801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 289368090919844653527295469 108513034094941745072735801)
      ·
        refine ⟨81384775571206308804551851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108513034094941745072735801 81384775571206308804551851)
        ·
          refine ⟨122077163356809463206827777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81384775571206308804551851 122077163356809463206827777)
          ·
            refine ⟨91557872517607097405120833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 122077163356809463206827777 91557872517607097405120833)
            ·
              refine ⟨68668404388205323053840625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91557872517607097405120833 68668404388205323053840625)
              ·
                refine ⟨51501303291153992290380469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68668404388205323053840625 51501303291153992290380469)
                ·
                  refine ⟨4828247183545686777223169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 51501303291153992290380469 4828247183545686777223169)
                  ·
                    refine ⟨3621185387659265082917377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4828247183545686777223169 3621185387659265082917377)
                    ·
                      refine ⟨2715889040744448812188033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3621185387659265082917377 2715889040744448812188033)
                      ·
                        rfl

theorem cell23_5289175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 2, 5, 2, 2].length) (baseStart_5289175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5289175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5289175 prefixEnd_5289175 := by exact prefixLift 5289175
  have htrace : WordTrace (prefixWord ++ tailWord_5289175) baseStart_5289175 baseEnd_5289175 := by
    simpa [prefixWord, tailWord_5289175, baseEnd_5289175] using wordTrace_append hprefix tailTrace_5289175
  have hstable : (prefixWord ++ tailWord_5289175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5289175).length < 2 ^ (prefixWord ++ tailWord_5289175).sum := by decide
  have hdescent : baseEnd_5289175 < baseStart_5289175 := by decide
  rcases family_descends (prefixWord ++ tailWord_5289175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5289178 : List Nat := [3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 3]
def baseStart_5289178 : Nat := 118140960795 + 5289178 * 2 ^ 59
def prefixEnd_5289178 : Nat := 4983230072969 + 3 ^ 40 * 5289178 * 2
def baseEnd_5289178 : Nat := 2715890581186412300450519

theorem tailTrace_5289178 : CollatzResearch.WordTrace tailWord_5289178 prefixEnd_5289178 2715890581186412300450519 := by
  unfold tailWord_5289178
  simp only [CollatzResearch.WordTrace]
  refine ⟨48228042508054725132639047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128608113354812600353704125 48228042508054725132639047)
  ·
    refine ⟨72342063762082087698958571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48228042508054725132639047 72342063762082087698958571)
    ·
      refine ⟨108513095643123131548437857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72342063762082087698958571 108513095643123131548437857)
      ·
        refine ⟨81384821732342348661328393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108513095643123131548437857 81384821732342348661328393)
        ·
          refine ⟨61038616299256761495996295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81384821732342348661328393 61038616299256761495996295)
          ·
            refine ⟨91557924448885142243994443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61038616299256761495996295 91557924448885142243994443)
            ·
              refine ⟨137336886673327713365991665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91557924448885142243994443 137336886673327713365991665)
              ·
                refine ⟨103002665004995785024493749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 137336886673327713365991665 103002665004995785024493749)
                ·
                  refine ⟨9656499844218354846046289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 103002665004995785024493749 9656499844218354846046289)
                  ·
                    refine ⟨7242374883163766134534717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9656499844218354846046289 7242374883163766134534717)
                    ·
                      refine ⟨2715890581186412300450519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7242374883163766134534717 2715890581186412300450519)
                      ·
                        rfl

theorem cell23_5289178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 3].length) (baseStart_5289178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5289178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5289178 prefixEnd_5289178 := by exact prefixLift 5289178
  have htrace : WordTrace (prefixWord ++ tailWord_5289178) baseStart_5289178 baseEnd_5289178 := by
    simpa [prefixWord, tailWord_5289178, baseEnd_5289178] using wordTrace_append hprefix tailTrace_5289178
  have hstable : (prefixWord ++ tailWord_5289178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5289178).length < 2 ^ (prefixWord ++ tailWord_5289178).sum := by decide
  have hdescent : baseEnd_5289178 < baseStart_5289178 := by decide
  rcases family_descends (prefixWord ++ tailWord_5289178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5289201 : List Nat := [1, 2, 2, 2, 2, 1, 1, 1, 1, 4, 6]
def baseStart_5289201 : Nat := 118140960795 + 5289201 * 2 ^ 59
def prefixEnd_5289201 : Nat := 4983230072969 + 3 ^ 40 * 5289201 * 2
def baseEnd_5289201 : Nat := 2715902391241465710462913

theorem tailTrace_5289201 : CollatzResearch.WordTrace tailWord_5289201 prefixEnd_5289201 2715902391241465710462913 := by
  unfold tailWord_5289201
  simp only [CollatzResearch.WordTrace]
  refine ⟨192913008911135575458643457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128608672607423716972428971 192913008911135575458643457)
  ·
    refine ⟨144684756683351681593982593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192913008911135575458643457 144684756683351681593982593)
    ·
      refine ⟨108513567512513761195486945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144684756683351681593982593 108513567512513761195486945)
      ·
        refine ⟨81385175634385320896615209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108513567512513761195486945 81385175634385320896615209)
        ·
          refine ⟨61038881725788990672461407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81385175634385320896615209 61038881725788990672461407)
          ·
            refine ⟨91558322588683486008692111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61038881725788990672461407 91558322588683486008692111)
            ·
              refine ⟨137337483883025229013038167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91558322588683486008692111 137337483883025229013038167)
              ·
                refine ⟨206006225824537843519557251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 137337483883025229013038167 206006225824537843519557251)
                ·
                  refine ⟨309009338736806765279335877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 206006225824537843519557251 309009338736806765279335877)
                  ·
                    refine ⟨57939251013151268489875477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 309009338736806765279335877 57939251013151268489875477)
                    ·
                      refine ⟨2715902391241465710462913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 57939251013151268489875477 2715902391241465710462913)
                      ·
                        rfl

theorem cell23_5289201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 1, 1, 4, 6].length) (baseStart_5289201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5289201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5289201 prefixEnd_5289201 := by exact prefixLift 5289201
  have htrace : WordTrace (prefixWord ++ tailWord_5289201) baseStart_5289201 baseEnd_5289201 := by
    simpa [prefixWord, tailWord_5289201, baseEnd_5289201] using wordTrace_append hprefix tailTrace_5289201
  have hstable : (prefixWord ++ tailWord_5289201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5289201).length < 2 ^ (prefixWord ++ tailWord_5289201).sum := by decide
  have hdescent : baseEnd_5289201 < baseStart_5289201 := by decide
  rcases family_descends (prefixWord ++ tailWord_5289201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5289202 : List Nat := [3, 2, 1, 3, 3, 1, 1, 3, 2, 4]
def baseStart_5289202 : Nat := 118140960795 + 5289202 * 2 ^ 59
def prefixEnd_5289202 : Nat := 4983230072969 + 3 ^ 40 * 5289202 * 2
def baseEnd_5289202 : Nat := 905300968240706735516803

theorem tailTrace_5289202 : CollatzResearch.WordTrace tailWord_5289202 prefixEnd_5289202 905300968240706735516803 := by
  unfold tailWord_5289202
  simp only [CollatzResearch.WordTrace]
  refine ⟨48228261346032988157357465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128608696922754635086286573 48228261346032988157357465)
  ·
    refine ⟨36171196009524741118018099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48228261346032988157357465 36171196009524741118018099)
    ·
      refine ⟨54256794014287111677027149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36171196009524741118018099 54256794014287111677027149)
      ·
        refine ⟨20346297755357666878885181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54256794014287111677027149 20346297755357666878885181)
        ·
          refine ⟨7629861658259125079581943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20346297755357666878885181 7629861658259125079581943)
          ·
            refine ⟨11444792487388687619372915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7629861658259125079581943 11444792487388687619372915)
            ·
              refine ⟨17167188731083031429059373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11444792487388687619372915 17167188731083031429059373)
              ·
                refine ⟨6437695774156136785897265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17167188731083031429059373 6437695774156136785897265)
                ·
                  refine ⟨4828271830617102589422949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6437695774156136785897265 4828271830617102589422949)
                  ·
                    refine ⟨905300968240706735516803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4828271830617102589422949 905300968240706735516803)
                    ·
                      rfl

theorem cell23_5289202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 1, 3, 2, 4].length) (baseStart_5289202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5289202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5289202 prefixEnd_5289202 := by exact prefixLift 5289202
  have htrace : WordTrace (prefixWord ++ tailWord_5289202) baseStart_5289202 baseEnd_5289202 := by
    simpa [prefixWord, tailWord_5289202, baseEnd_5289202] using wordTrace_append hprefix tailTrace_5289202
  have hstable : (prefixWord ++ tailWord_5289202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5289202).length < 2 ^ (prefixWord ++ tailWord_5289202).sum := by decide
  have hdescent : baseEnd_5289202 < baseStart_5289202 := by decide
  rcases family_descends (prefixWord ++ tailWord_5289202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5289241 : List Nat := [1, 2, 1, 2, 1, 1, 1, 1, 5, 8]
def baseStart_5289241 : Nat := 118140960795 + 5289241 * 2 ^ 59
def prefixEnd_5289241 : Nat := 4983230072969 + 3 ^ 40 * 5289241 * 2
def baseEnd_5289241 : Nat := 905307643489215184654243

theorem tailTrace_5289241 : CollatzResearch.WordTrace tailWord_5289241 prefixEnd_5289241 905307643489215184654243 := by
  unfold tailWord_5289241
  simp only [CollatzResearch.WordTrace]
  refine ⟨192914467830990662290099577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128609645220660441526733051 192914467830990662290099577)
  ·
    refine ⟨144685850873242996717574683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192914467830990662290099577 144685850873242996717574683)
    ·
      refine ⟨217028776309864495076362025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144685850873242996717574683 217028776309864495076362025)
      ·
        refine ⟨162771582232398371307271519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 217028776309864495076362025 162771582232398371307271519)
        ·
          refine ⟨244157373348597556960907279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162771582232398371307271519 244157373348597556960907279)
          ·
            refine ⟨366236060022896335441360919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 244157373348597556960907279 366236060022896335441360919)
            ·
              refine ⟨549354090034344503162041379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 366236060022896335441360919 549354090034344503162041379)
              ·
                refine ⟨824031135051516754743062069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 549354090034344503162041379 824031135051516754743062069)
                ·
                  refine ⟨77252918911079695757162069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 824031135051516754743062069 77252918911079695757162069)
                  ·
                    refine ⟨905307643489215184654243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 77252918911079695757162069 905307643489215184654243)
                    ·
                      rfl

theorem cell23_5289241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 5, 8].length) (baseStart_5289241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5289241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5289241 prefixEnd_5289241 := by exact prefixLift 5289241
  have htrace : WordTrace (prefixWord ++ tailWord_5289241) baseStart_5289241 baseEnd_5289241 := by
    simpa [prefixWord, tailWord_5289241, baseEnd_5289241] using wordTrace_append hprefix tailTrace_5289241
  have hstable : (prefixWord ++ tailWord_5289241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5289241).length < 2 ^ (prefixWord ++ tailWord_5289241).sum := by decide
  have hdescent : baseEnd_5289241 < baseStart_5289241 := by decide
  rcases family_descends (prefixWord ++ tailWord_5289241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5289242 : List Nat := [3, 1, 1, 3, 3, 1, 1, 4, 2, 1, 3]
def baseStart_5289242 : Nat := 118140960795 + 5289242 * 2 ^ 59
def prefixEnd_5289242 : Nat := 4983230072969 + 3 ^ 40 * 5289242 * 2
def baseEnd_5289242 : Nat := 2715923443948300050050225

theorem tailTrace_5289242 : CollatzResearch.WordTrace tailWord_5289242 prefixEnd_5289242 2715923443948300050050225 := by
  unfold tailWord_5289242
  simp only [CollatzResearch.WordTrace]
  refine ⟨48228626075996759865221495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128609669535991359640590653 48228626075996759865221495)
  ·
    refine ⟨72342939113995139797832243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48228626075996759865221495 72342939113995139797832243)
    ·
      refine ⟨108514408670992709696748365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72342939113995139797832243 108514408670992709696748365)
      ·
        refine ⟨40692903251622266136280637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 108514408670992709696748365 40692903251622266136280637)
        ·
          refine ⟨15259838719358349801105239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40692903251622266136280637 15259838719358349801105239)
          ·
            refine ⟨22889758079037524701657859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15259838719358349801105239 22889758079037524701657859)
            ·
              refine ⟨34334637118556287052486789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22889758079037524701657859 34334637118556287052486789)
              ·
                refine ⟨6437744459729303822341273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34334637118556287052486789 6437744459729303822341273)
                ·
                  refine ⟨4828308344796977866755955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6437744459729303822341273 4828308344796977866755955)
                  ·
                    refine ⟨7242462517195466800133933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4828308344796977866755955 7242462517195466800133933)
                    ·
                      refine ⟨2715923443948300050050225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7242462517195466800133933 2715923443948300050050225)
                      ·
                        rfl

theorem cell23_5289242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 4, 2, 1, 3].length) (baseStart_5289242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5289242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5289242 prefixEnd_5289242 := by exact prefixLift 5289242
  have htrace : WordTrace (prefixWord ++ tailWord_5289242) baseStart_5289242 baseEnd_5289242 := by
    simpa [prefixWord, tailWord_5289242, baseEnd_5289242] using wordTrace_append hprefix tailTrace_5289242
  have hstable : (prefixWord ++ tailWord_5289242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5289242).length < 2 ^ (prefixWord ++ tailWord_5289242).sum := by decide
  have hdescent : baseEnd_5289242 < baseStart_5289242 := by decide
  rcases family_descends (prefixWord ++ tailWord_5289242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5289293 : List Nat := [1, 6, 1, 3, 1, 2, 1, 2, 2, 1, 3]
def baseStart_5289293 : Nat := 118140960795 + 5289293 * 2 ^ 59
def prefixEnd_5289293 : Nat := 4983230072969 + 3 ^ 40 * 5289293 * 2
def baseEnd_5289293 : Nat := 2715949631461679350512491

theorem tailTrace_5289293 : CollatzResearch.WordTrace tailWord_5289293 prefixEnd_5289293 2715949631461679350512491 := by
  unfold tailWord_5289293
  simp only [CollatzResearch.WordTrace]
  refine ⟨192916364426802275170992533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128610909617868183447328355 192916364426802275170992533)
  ·
    refine ⟨9042954582506356648640275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 192916364426802275170992533 9042954582506356648640275)
    ·
      refine ⟨13564431873759534972960413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9042954582506356648640275 13564431873759534972960413)
      ·
        refine ⟨5086661952659825614860155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13564431873759534972960413 5086661952659825614860155)
        ·
          refine ⟨7629992928989738422290233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5086661952659825614860155 7629992928989738422290233)
          ·
            refine ⟨5722494696742303816717675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7629992928989738422290233 5722494696742303816717675)
            ·
              refine ⟨8583742045113455725076513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5722494696742303816717675 8583742045113455725076513)
              ·
                refine ⟨6437806533835091793807385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8583742045113455725076513 6437806533835091793807385)
                ·
                  refine ⟨4828354900376318845355539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6437806533835091793807385 4828354900376318845355539)
                  ·
                    refine ⟨7242532350564478268033309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4828354900376318845355539 7242532350564478268033309)
                    ·
                      refine ⟨2715949631461679350512491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7242532350564478268033309 2715949631461679350512491)
                      ·
                        rfl

theorem cell23_5289293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 1, 2, 2, 1, 3].length) (baseStart_5289293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5289293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5289293 prefixEnd_5289293 := by exact prefixLift 5289293
  have htrace : WordTrace (prefixWord ++ tailWord_5289293) baseStart_5289293 baseEnd_5289293 := by
    simpa [prefixWord, tailWord_5289293, baseEnd_5289293] using wordTrace_append hprefix tailTrace_5289293
  have hstable : (prefixWord ++ tailWord_5289293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5289293).length < 2 ^ (prefixWord ++ tailWord_5289293).sum := by decide
  have hdescent : baseEnd_5289293 < baseStart_5289293 := by decide
  rcases family_descends (prefixWord ++ tailWord_5289293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5289305 : List Nat := [1, 2, 1, 2, 2, 2, 4, 4, 5]
def baseStart_5289305 : Nat := 118140960795 + 5289305 * 2 ^ 59
def prefixEnd_5289305 : Nat := 4983230072969 + 3 ^ 40 * 5289305 * 2
def baseEnd_5289305 : Nat := 301772865914392589284715

theorem tailTrace_5289305 : CollatzResearch.WordTrace tailWord_5289305 prefixEnd_5289305 301772865914392589284715 := by
  unfold tailWord_5289305
  simp only [CollatzResearch.WordTrace]
  refine ⟨192916802102758801220429369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128611201401839200813619579 192916802102758801220429369)
  ·
    refine ⟨144687601577069100915322027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192916802102758801220429369 144687601577069100915322027)
    ·
      refine ⟨217031402365603651372983041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144687601577069100915322027 217031402365603651372983041)
      ·
        refine ⟨162773551774202738529737281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 217031402365603651372983041 162773551774202738529737281)
        ·
          refine ⟨122080163830652053897302961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 162773551774202738529737281 122080163830652053897302961)
          ·
            refine ⟨91560122872989040422977221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 122080163830652053897302961 91560122872989040422977221)
            ·
              refine ⟨17167523038685445079308229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 91560122872989040422977221 17167523038685445079308229)
              ·
                refine ⟨3218910569753520952370293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17167523038685445079308229 3218910569753520952370293)
                ·
                  refine ⟨301772865914392589284715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3218910569753520952370293 301772865914392589284715)
                  ·
                    rfl

theorem cell23_5289305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 4, 4, 5].length) (baseStart_5289305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5289305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5289305 prefixEnd_5289305 := by exact prefixLift 5289305
  have htrace : WordTrace (prefixWord ++ tailWord_5289305) baseStart_5289305 baseEnd_5289305 := by
    simpa [prefixWord, tailWord_5289305, baseEnd_5289305] using wordTrace_append hprefix tailTrace_5289305
  have hstable : (prefixWord ++ tailWord_5289305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5289305).length < 2 ^ (prefixWord ++ tailWord_5289305).sum := by decide
  have hdescent : baseEnd_5289305 < baseStart_5289305 := by decide
  rcases family_descends (prefixWord ++ tailWord_5289305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5289315 : List Nat := [1, 1, 1, 5, 2, 2, 2, 1, 2, 3, 3]
def baseStart_5289315 : Nat := 118140960795 + 5289315 * 2 ^ 59
def prefixEnd_5289315 : Nat := 4983230072969 + 3 ^ 40 * 5289315 * 2
def baseEnd_5289315 : Nat := 2715960928036078264437389

theorem tailTrace_5289315 : CollatzResearch.WordTrace tailWord_5289315 prefixEnd_5289315 2715960928036078264437389 := by
  unfold tailWord_5289315
  simp only [CollatzResearch.WordTrace]
  refine ⟨192917166832722572928293399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128611444555148381952195599 192917166832722572928293399)
  ·
    refine ⟨289375750249083859392440099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192917166832722572928293399 289375750249083859392440099)
    ·
      refine ⟨434063625373625789088660149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 289375750249083859392440099 434063625373625789088660149)
      ·
        refine ⟨40693464878777417727061889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 434063625373625789088660149 40693464878777417727061889)
        ·
          refine ⟨30520098659083063295296417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40693464878777417727061889 30520098659083063295296417)
          ·
            refine ⟨22890073994312297471472313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30520098659083063295296417 22890073994312297471472313)
            ·
              refine ⟨17167555495734223103604235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22890073994312297471472313 17167555495734223103604235)
              ·
                refine ⟨25751333243601334655406353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17167555495734223103604235 25751333243601334655406353)
                ·
                  refine ⟨19313499932701000991554765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25751333243601334655406353 19313499932701000991554765)
                  ·
                    refine ⟨7242562474762875371833037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19313499932701000991554765 7242562474762875371833037)
                    ·
                      refine ⟨2715960928036078264437389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7242562474762875371833037 2715960928036078264437389)
                      ·
                        rfl

theorem cell23_5289315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 2, 1, 2, 3, 3].length) (baseStart_5289315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5289315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5289315 prefixEnd_5289315 := by exact prefixLift 5289315
  have htrace : WordTrace (prefixWord ++ tailWord_5289315) baseStart_5289315 baseEnd_5289315 := by
    simpa [prefixWord, tailWord_5289315, baseEnd_5289315] using wordTrace_append hprefix tailTrace_5289315
  have hstable : (prefixWord ++ tailWord_5289315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5289315).length < 2 ^ (prefixWord ++ tailWord_5289315).sum := by decide
  have hdescent : baseEnd_5289315 < baseStart_5289315 := by decide
  rcases family_descends (prefixWord ++ tailWord_5289315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5289316 : List Nat := [2, 3, 1, 1, 3, 3, 3, 1, 2, 2, 2]
def baseStart_5289316 : Nat := 118140960795 + 5289316 * 2 ^ 59
def prefixEnd_5289316 : Nat := 4983230072969 + 3 ^ 40 * 5289316 * 2
def baseEnd_5289316 : Nat := 2715961441516732760524885

theorem tailTrace_5289316 : CollatzResearch.WordTrace tailWord_5289316 prefixEnd_5289316 2715961441516732760524885 := by
  unfold tailWord_5289316
  simp only [CollatzResearch.WordTrace]
  refine ⟨96458601652859475049539901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128611468870479300066053201 96458601652859475049539901)
  ·
    refine ⟨36171975619822303143577463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96458601652859475049539901 36171975619822303143577463)
    ·
      refine ⟨54257963429733454715366195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36171975619822303143577463 54257963429733454715366195)
      ·
        refine ⟨81386945144600182073049293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54257963429733454715366195 81386945144600182073049293)
        ·
          refine ⟨30520104429225068277393485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81386945144600182073049293 30520104429225068277393485)
          ·
            refine ⟨11445039160959400604022557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30520104429225068277393485 11445039160959400604022557)
            ·
              refine ⟨4291889685359775226508459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11445039160959400604022557 4291889685359775226508459)
              ·
                refine ⟨6437834528039662839762689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4291889685359775226508459 6437834528039662839762689)
                ·
                  refine ⟨4828375896029747129822017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6437834528039662839762689 4828375896029747129822017)
                  ·
                    refine ⟨3621281922022310347366513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4828375896029747129822017 3621281922022310347366513)
                    ·
                      refine ⟨2715961441516732760524885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3621281922022310347366513 2715961441516732760524885)
                      ·
                        rfl

theorem cell23_5289316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 3, 1, 2, 2, 2].length) (baseStart_5289316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5289316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5289316 prefixEnd_5289316 := by exact prefixLift 5289316
  have htrace : WordTrace (prefixWord ++ tailWord_5289316) baseStart_5289316 baseEnd_5289316 := by
    simpa [prefixWord, tailWord_5289316, baseEnd_5289316] using wordTrace_append hprefix tailTrace_5289316
  have hstable : (prefixWord ++ tailWord_5289316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5289316).length < 2 ^ (prefixWord ++ tailWord_5289316).sum := by decide
  have hdescent : baseEnd_5289316 < baseStart_5289316 := by decide
  rcases family_descends (prefixWord ++ tailWord_5289316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5289355 : List Nat := [1, 1, 1, 1, 4, 3, 3, 2, 2, 1, 4]
def baseStart_5289355 : Nat := 118140960795 + 5289355 * 2 ^ 59
def prefixEnd_5289355 : Nat := 4983230072969 + 3 ^ 40 * 5289355 * 2
def baseEnd_5289355 : Nat := 2715981467262258107937205

theorem tailTrace_5289355 : CollatzResearch.WordTrace tailWord_5289355 prefixEnd_5289355 2715981467262258107937205 := by
  unfold tailWord_5289355
  simp only [CollatzResearch.WordTrace]
  refine ⟨192918625752577659759749519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128612417168385106506499679 192918625752577659759749519)
  ·
    refine ⟨289377938628866489639624279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192918625752577659759749519 289377938628866489639624279)
    ·
      refine ⟨434066907943299734459436419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 289377938628866489639624279 434066907943299734459436419)
      ·
        refine ⟨651100361914949601689154629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 434066907943299734459436419 651100361914949601689154629)
        ·
          refine ⟨122081317859053050316716493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 651100361914949601689154629 122081317859053050316716493)
          ·
            refine ⟨45780494197144893868768685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 122081317859053050316716493 45780494197144893868768685)
            ·
              refine ⟨17167685323929335200788257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45780494197144893868768685 17167685323929335200788257)
              ·
                refine ⟨12875763992947001400591193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17167685323929335200788257 12875763992947001400591193)
                ·
                  refine ⟨9656822994710251050443395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12875763992947001400591193 9656822994710251050443395)
                  ·
                    refine ⟨14485234492065376575665093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9656822994710251050443395 14485234492065376575665093)
                    ·
                      refine ⟨2715981467262258107937205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14485234492065376575665093 2715981467262258107937205)
                      ·
                        rfl

theorem cell23_5289355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 3, 2, 2, 1, 4].length) (baseStart_5289355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5289355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5289355 prefixEnd_5289355 := by exact prefixLift 5289355
  have htrace : WordTrace (prefixWord ++ tailWord_5289355) baseStart_5289355 baseEnd_5289355 := by
    simpa [prefixWord, tailWord_5289355, baseEnd_5289355] using wordTrace_append hprefix tailTrace_5289355
  have hstable : (prefixWord ++ tailWord_5289355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5289355).length < 2 ^ (prefixWord ++ tailWord_5289355).sum := by decide
  have hdescent : baseEnd_5289355 < baseStart_5289355 := by decide
  rcases family_descends (prefixWord ++ tailWord_5289355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5289389 : List Nat := [1, 5, 2, 2, 1, 2, 2, 1, 2, 1, 4]
def baseStart_5289389 : Nat := 118140960795 + 5289389 * 2 ^ 59
def prefixEnd_5289389 : Nat := 4983230072969 + 3 ^ 40 * 5289389 * 2
def baseEnd_5289389 : Nat := 2715998925604510974912049

theorem tailTrace_5289389 : CollatzResearch.WordTrace tailWord_5289389 prefixEnd_5289389 2715998925604510974912049 := by
  unfold tailWord_5289389
  simp only [CollatzResearch.WordTrace]
  refine ⟨192919865834454483566487221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128613243889636322377658147 192919865834454483566487221)
  ·
    refine ⟨18086237421980107834358177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 192919865834454483566487221 18086237421980107834358177)
    ·
      refine ⟨13564678066485080875768633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18086237421980107834358177 13564678066485080875768633)
      ·
        refine ⟨10173508549863810656826475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13564678066485080875768633 10173508549863810656826475)
        ·
          refine ⟨15260262824795715985239713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10173508549863810656826475 15260262824795715985239713)
          ·
            refine ⟨11445197118596786988929785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15260262824795715985239713 11445197118596786988929785)
            ·
              refine ⟨8583897838947590241697339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11445197118596786988929785 8583897838947590241697339)
              ·
                refine ⟨12875846758421385362546009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8583897838947590241697339 12875846758421385362546009)
                ·
                  refine ⟨9656885068816039021909507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12875846758421385362546009 9656885068816039021909507)
                  ·
                    refine ⟨14485327603224058532864261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9656885068816039021909507 14485327603224058532864261)
                    ·
                      refine ⟨2715998925604510974912049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14485327603224058532864261 2715998925604510974912049)
                      ·
                        rfl

theorem cell23_5289389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 2, 1, 2, 1, 4].length) (baseStart_5289389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5289389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5289389 prefixEnd_5289389 := by exact prefixLift 5289389
  have htrace : WordTrace (prefixWord ++ tailWord_5289389) baseStart_5289389 baseEnd_5289389 := by
    simpa [prefixWord, tailWord_5289389, baseEnd_5289389] using wordTrace_append hprefix tailTrace_5289389
  have hstable : (prefixWord ++ tailWord_5289389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5289389).length < 2 ^ (prefixWord ++ tailWord_5289389).sum := by decide
  have hdescent : baseEnd_5289389 < baseStart_5289389 := by decide
  rcases family_descends (prefixWord ++ tailWord_5289389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5289412 : List Nat := [2, 3, 3, 2, 1, 1, 1, 4, 6]
def baseStart_5289412 : Nat := 118140960795 + 5289412 * 2 ^ 59
def prefixEnd_5289412 : Nat := 4983230072969 + 3 ^ 40 * 5289412 * 2
def baseEnd_5289412 : Nat := 301778970628840487213827

theorem tailTrace_5289412 : CollatzResearch.WordTrace tailWord_5289412 prefixEnd_5289412 301778970628840487213827 := by
  unfold tailWord_5289412
  simp only [CollatzResearch.WordTrace]
  refine ⟨96460352356685579247287245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128613803142247438996382993 96460352356685579247287245)
  ·
    refine ⟨36172632133757092217732717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96460352356685579247287245 36172632133757092217732717)
    ·
      refine ⟨13564737050158909581649769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36172632133757092217732717 13564737050158909581649769)
      ·
        refine ⟨10173552787619182186237327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13564737050158909581649769 10173552787619182186237327)
        ·
          refine ⟨15260329181428773279355991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10173552787619182186237327 15260329181428773279355991)
          ·
            refine ⟨22890493772143159919033987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15260329181428773279355991 22890493772143159919033987)
            ·
              refine ⟨34335740658214739878550981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22890493772143159919033987 34335740658214739878550981)
              ·
                refine ⟨6437951373415263727228309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34335740658214739878550981 6437951373415263727228309)
                ·
                  refine ⟨301778970628840487213827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6437951373415263727228309 301778970628840487213827)
                  ·
                    rfl

theorem cell23_5289412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 4, 6].length) (baseStart_5289412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5289412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5289412 prefixEnd_5289412 := by exact prefixLift 5289412
  have htrace : WordTrace (prefixWord ++ tailWord_5289412) baseStart_5289412 baseEnd_5289412 := by
    simpa [prefixWord, tailWord_5289412, baseEnd_5289412] using wordTrace_append hprefix tailTrace_5289412
  have hstable : (prefixWord ++ tailWord_5289412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5289412).length < 2 ^ (prefixWord ++ tailWord_5289412).sum := by decide
  have hdescent : baseEnd_5289412 < baseStart_5289412 := by decide
  rcases family_descends (prefixWord ++ tailWord_5289412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5289432 : List Nat := [2, 1, 2, 2, 2, 1, 2, 2, 4, 3, 2]
def baseStart_5289432 : Nat := 118140960795 + 5289432 * 2 ^ 59
def prefixEnd_5289432 : Nat := 4983230072969 + 3 ^ 40 * 5289432 * 2
def baseEnd_5289432 : Nat := 2716021005272654306674351

theorem tailTrace_5289432 : CollatzResearch.WordTrace tailWord_5289432 prefixEnd_5289432 2716021005272654306674351 := by
  unfold tailWord_5289432
  simp only [CollatzResearch.WordTrace]
  refine ⟨96460717086649350955151275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128614289448865801273535033 96460717086649350955151275)
  ·
    refine ⟨144691075629974026432726913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96460717086649350955151275 144691075629974026432726913)
    ·
      refine ⟨108518306722480519824545185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144691075629974026432726913 108518306722480519824545185)
      ·
        refine ⟨81388730041860389868408889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108518306722480519824545185 81388730041860389868408889)
        ·
          refine ⟨61041547531395292401306667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81388730041860389868408889 61041547531395292401306667)
          ·
            refine ⟨91562321297092938601960001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61041547531395292401306667 91562321297092938601960001)
            ·
              refine ⟨68671740972819703951470001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91562321297092938601960001 68671740972819703951470001)
              ·
                refine ⟨51503805729614777963602501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68671740972819703951470001 51503805729614777963602501)
                ·
                  refine ⟨9656963574302770868175469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 51503805729614777963602501 9656963574302770868175469)
                  ·
                    refine ⟨3621361340363539075565801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9656963574302770868175469 3621361340363539075565801)
                    ·
                      refine ⟨2716021005272654306674351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3621361340363539075565801 2716021005272654306674351)
                      ·
                        rfl

theorem cell23_5289432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 2, 4, 3, 2].length) (baseStart_5289432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5289432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5289432 prefixEnd_5289432 := by exact prefixLift 5289432
  have htrace : WordTrace (prefixWord ++ tailWord_5289432) baseStart_5289432 baseEnd_5289432 := by
    simpa [prefixWord, tailWord_5289432, baseEnd_5289432] using wordTrace_append hprefix tailTrace_5289432
  have hstable : (prefixWord ++ tailWord_5289432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5289432).length < 2 ^ (prefixWord ++ tailWord_5289432).sum := by decide
  have hdescent : baseEnd_5289432 < baseStart_5289432 := by decide
  rcases family_descends (prefixWord ++ tailWord_5289432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5289455 : List Nat := [1, 1, 2, 1, 4, 1, 4, 2, 1, 6]
def baseStart_5289455 : Nat := 118140960795 + 5289455 * 2 ^ 59
def prefixEnd_5289455 : Nat := 4983230072969 + 3 ^ 40 * 5289455 * 2
def baseEnd_5289455 : Nat := 905344271775902572228915

theorem tailTrace_5289455 : CollatzResearch.WordTrace tailWord_5289455 prefixEnd_5289455 905344271775902572228915 := by
  unfold tailWord_5289455
  simp only [CollatzResearch.WordTrace]
  refine ⟨192922273052215376838389819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128614848701476917892259879 192922273052215376838389819)
  ·
    refine ⟨289383409578323065257584729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192922273052215376838389819 289383409578323065257584729)
    ·
      refine ⟨217037557183742298943188547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 289383409578323065257584729 217037557183742298943188547)
      ·
        refine ⟨325556335775613448414782821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 217037557183742298943188547 325556335775613448414782821)
        ·
          refine ⟨61041812957927521577771779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 325556335775613448414782821 61041812957927521577771779)
          ·
            refine ⟨91562719436891282366657669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61041812957927521577771779 91562719436891282366657669)
            ·
              refine ⟨17168009894417115443748313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 91562719436891282366657669 17168009894417115443748313)
              ·
                refine ⟨12876007420812836582811235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17168009894417115443748313 12876007420812836582811235)
                ·
                  refine ⟨19314011131219254874216853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12876007420812836582811235 19314011131219254874216853)
                  ·
                    refine ⟨905344271775902572228915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19314011131219254874216853 905344271775902572228915)
                    ·
                      rfl

theorem cell23_5289455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 4, 2, 1, 6].length) (baseStart_5289455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5289455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5289455 prefixEnd_5289455 := by exact prefixLift 5289455
  have htrace : WordTrace (prefixWord ++ tailWord_5289455) baseStart_5289455 baseEnd_5289455 := by
    simpa [prefixWord, tailWord_5289455, baseEnd_5289455] using wordTrace_append hprefix tailTrace_5289455
  have hstable : (prefixWord ++ tailWord_5289455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5289455).length < 2 ^ (prefixWord ++ tailWord_5289455).sum := by decide
  have hdescent : baseEnd_5289455 < baseStart_5289455 := by decide
  rcases family_descends (prefixWord ++ tailWord_5289455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5289456 : List Nat := [2, 1, 1, 1, 3, 5, 2, 3, 1, 1, 3]
def baseStart_5289456 : Nat := 118140960795 + 5289456 * 2 ^ 59
def prefixEnd_5289456 : Nat := 4983230072969 + 3 ^ 40 * 5289456 * 2
def baseEnd_5289456 : Nat := 2716033328808362212774241

theorem tailTrace_5289456 : CollatzResearch.WordTrace tailWord_5289456 prefixEnd_5289456 2716033328808362212774241 := by
  unfold tailWord_5289456
  simp only [CollatzResearch.WordTrace]
  refine ⟨96461154762605877004588111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128614873016807836006117481 96461154762605877004588111)
  ·
    refine ⟨144691732143908815506882167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96461154762605877004588111 144691732143908815506882167)
    ·
      refine ⟨217037598215863223260323251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144691732143908815506882167 217037598215863223260323251)
      ·
        refine ⟨325556397323794834890484877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 217037598215863223260323251 325556397323794834890484877)
        ·
          refine ⟨122083648996423063083931829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 325556397323794834890484877 122083648996423063083931829)
          ·
            refine ⟨11445342093414662164118609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 122083648996423063083931829 11445342093414662164118609)
            ·
              refine ⟨8584006570060996623088957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11445342093414662164118609 8584006570060996623088957)
              ·
                refine ⟨3219002463772873733658359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8584006570060996623088957 3219002463772873733658359)
                ·
                  refine ⟨4828503695659310600487539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3219002463772873733658359 4828503695659310600487539)
                  ·
                    refine ⟨7242755543488965900731309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4828503695659310600487539 7242755543488965900731309)
                    ·
                      refine ⟨2716033328808362212774241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7242755543488965900731309 2716033328808362212774241)
                      ·
                        rfl

theorem cell23_5289456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 2, 3, 1, 1, 3].length) (baseStart_5289456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5289456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5289456 prefixEnd_5289456 := by exact prefixLift 5289456
  have htrace : WordTrace (prefixWord ++ tailWord_5289456) baseStart_5289456 baseEnd_5289456 := by
    simpa [prefixWord, tailWord_5289456, baseEnd_5289456] using wordTrace_append hprefix tailTrace_5289456
  have hstable : (prefixWord ++ tailWord_5289456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5289456).length < 2 ^ (prefixWord ++ tailWord_5289456).sum := by decide
  have hdescent : baseEnd_5289456 < baseStart_5289456 := by decide
  rcases family_descends (prefixWord ++ tailWord_5289456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5289465 : List Nat := [1, 2, 1, 3, 1, 2, 1, 5, 1, 1, 5]
def baseStart_5289465 : Nat := 118140960795 + 5289465 * 2 ^ 59
def prefixEnd_5289465 : Nat := 4983230072969 + 3 ^ 40 * 5289465 * 2
def baseEnd_5289465 : Nat := 2716037950134252677561699

theorem tailTrace_5289465 : CollatzResearch.WordTrace tailWord_5289465 prefixEnd_5289465 2716037950134252677561699 := by
  unfold tailWord_5289465
  simp only [CollatzResearch.WordTrace]
  refine ⟨192922637782179148546253849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128615091854786099030835899 192922637782179148546253849)
  ·
    refine ⟨144691978336634361409690387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192922637782179148546253849 144691978336634361409690387)
    ·
      refine ⟨217037967504951542114535581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144691978336634361409690387 217037967504951542114535581)
      ·
        refine ⟨81389237814356828292950843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 217037967504951542114535581 81389237814356828292950843)
        ·
          refine ⟨122083856721535242439426265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81389237814356828292950843 122083856721535242439426265)
          ·
            refine ⟨91562892541151431829569699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 122083856721535242439426265 91562892541151431829569699)
            ·
              refine ⟨137344338811727147744354549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91562892541151431829569699 137344338811727147744354549)
              ·
                refine ⟨12876031763599420101033239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 137344338811727147744354549 12876031763599420101033239)
                ·
                  refine ⟨19314047645399130151549859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12876031763599420101033239 19314047645399130151549859)
                  ·
                    refine ⟨28971071468098695227324789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19314047645399130151549859 28971071468098695227324789)
                    ·
                      refine ⟨2716037950134252677561699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28971071468098695227324789 2716037950134252677561699)
                      ·
                        rfl

theorem cell23_5289465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 5, 1, 1, 5].length) (baseStart_5289465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5289465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5289465 prefixEnd_5289465 := by exact prefixLift 5289465
  have htrace : WordTrace (prefixWord ++ tailWord_5289465) baseStart_5289465 baseEnd_5289465 := by
    simpa [prefixWord, tailWord_5289465, baseEnd_5289465] using wordTrace_append hprefix tailTrace_5289465
  have hstable : (prefixWord ++ tailWord_5289465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5289465).length < 2 ^ (prefixWord ++ tailWord_5289465).sum := by decide
  have hdescent : baseEnd_5289465 < baseStart_5289465 := by decide
  rcases family_descends (prefixWord ++ tailWord_5289465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5289482 : List Nat := [3, 1, 2, 2, 2, 3, 1, 2, 1, 1, 5]
def baseStart_5289482 : Nat := 118140960795 + 5289482 * 2 ^ 59
def prefixEnd_5289482 : Nat := 4983230072969 + 3 ^ 40 * 5289482 * 2
def baseEnd_5289482 : Nat := 2716046679305379111049121

theorem tailTrace_5289482 : CollatzResearch.WordTrace tailWord_5289482 prefixEnd_5289482 2716046679305379111049121 := by
  unfold tailWord_5289482
  simp only [CollatzResearch.WordTrace]
  refine ⟨48230814455779390112405675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128615505215411706966415133 48230814455779390112405675)
  ·
    refine ⟨72346221683669085168608513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48230814455779390112405675 72346221683669085168608513)
    ·
      refine ⟨54259666262751813876456385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72346221683669085168608513 54259666262751813876456385)
      ·
        refine ⟨40694749697063860407342289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54259666262751813876456385 40694749697063860407342289)
        ·
          refine ⟨30521062272797895305506717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40694749697063860407342289 30521062272797895305506717)
          ·
            refine ⟨11445398352299210739565019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30521062272797895305506717 11445398352299210739565019)
            ·
              refine ⟨17168097528448816109347529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11445398352299210739565019 17168097528448816109347529)
              ·
                refine ⟨12876073146336612082010647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17168097528448816109347529 12876073146336612082010647)
                ·
                  refine ⟨19314109719504918123015971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12876073146336612082010647 19314109719504918123015971)
                  ·
                    refine ⟨28971164579257377184523957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19314109719504918123015971 28971164579257377184523957)
                    ·
                      refine ⟨2716046679305379111049121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28971164579257377184523957 2716046679305379111049121)
                      ·
                        rfl

theorem cell23_5289482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 1, 2, 1, 1, 5].length) (baseStart_5289482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5289482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5289482 prefixEnd_5289482 := by exact prefixLift 5289482
  have htrace : WordTrace (prefixWord ++ tailWord_5289482) baseStart_5289482 baseEnd_5289482 := by
    simpa [prefixWord, tailWord_5289482, baseEnd_5289482] using wordTrace_append hprefix tailTrace_5289482
  have hstable : (prefixWord ++ tailWord_5289482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5289482).length < 2 ^ (prefixWord ++ tailWord_5289482).sum := by decide
  have hdescent : baseEnd_5289482 < baseStart_5289482 := by decide
  rcases family_descends (prefixWord ++ tailWord_5289482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5289489 : List Nat := [1, 2, 2, 1, 1, 2, 7, 1, 2, 4]
def baseStart_5289489 : Nat := 118140960795 + 5289489 * 2 ^ 59
def prefixEnd_5289489 : Nat := 4983230072969 + 3 ^ 40 * 5289489 * 2
def baseEnd_5289489 : Nat := 905350091223320194553863

theorem tailTrace_5289489 : CollatzResearch.WordTrace tailWord_5289489 prefixEnd_5289489 905350091223320194553863 := by
  unfold tailWord_5289489
  simp only [CollatzResearch.WordTrace]
  refine ⟨192923513134092200645127521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128615675422728133763418347 192923513134092200645127521)
  ·
    refine ⟨144692634850569150483845641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192923513134092200645127521 144692634850569150483845641)
    ·
      refine ⟨108519476137926862862884231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144692634850569150483845641 108519476137926862862884231)
      ·
        refine ⟨162779214206890294294326347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108519476137926862862884231 162779214206890294294326347)
        ·
          refine ⟨244168821310335441441489521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162779214206890294294326347 244168821310335441441489521)
          ·
            refine ⟨183126615982751581081117141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 244168821310335441441489521 183126615982751581081117141)
            ·
              refine ⟨4292030062095740181588683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 183126615982751581081117141 4292030062095740181588683)
              ·
                refine ⟨6438045093143610272383025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4292030062095740181588683 6438045093143610272383025)
                ·
                  refine ⟨4828533819857707704287269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6438045093143610272383025 4828533819857707704287269)
                  ·
                    refine ⟨905350091223320194553863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4828533819857707704287269 905350091223320194553863)
                    ·
                      rfl

theorem cell23_5289489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 7, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 7, 1, 2, 4].length) (baseStart_5289489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5289489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5289489 prefixEnd_5289489 := by exact prefixLift 5289489
  have htrace : WordTrace (prefixWord ++ tailWord_5289489) baseStart_5289489 baseEnd_5289489 := by
    simpa [prefixWord, tailWord_5289489, baseEnd_5289489] using wordTrace_append hprefix tailTrace_5289489
  have hstable : (prefixWord ++ tailWord_5289489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5289489).length < 2 ^ (prefixWord ++ tailWord_5289489).sum := by decide
  have hdescent : baseEnd_5289489 < baseStart_5289489 := by decide
  rcases family_descends (prefixWord ++ tailWord_5289489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5289529 : List Nat := [1, 2, 1, 5, 1, 2, 2, 1, 4, 1, 3]
def baseStart_5289529 : Nat := 118140960795 + 5289529 * 2 ^ 59
def prefixEnd_5289529 : Nat := 4983230072969 + 3 ^ 40 * 5289529 * 2
def baseEnd_5289529 : Nat := 2716070812896140427161405

theorem tailTrace_5289529 : CollatzResearch.WordTrace tailWord_5289529 prefixEnd_5289529 2716070812896140427161405 := by
  unfold tailWord_5289529
  simp only [CollatzResearch.WordTrace]
  refine ⟨192924972053947287476583641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128616648035964858317722427 192924972053947287476583641)
  ·
    refine ⟨144693729040460465607437731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192924972053947287476583641 144693729040460465607437731)
    ·
      refine ⟨217040593560690698411156597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144693729040460465607437731 217040593560690698411156597)
      ·
        refine ⟨20347555646314752976045931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 217040593560690698411156597 20347555646314752976045931)
        ·
          refine ⟨30521333469472129464068897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20347555646314752976045931 30521333469472129464068897)
          ·
            refine ⟨22891000102104097098051673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30521333469472129464068897 22891000102104097098051673)
            ·
              refine ⟨17168250076578072823538755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22891000102104097098051673 17168250076578072823538755)
              ·
                refine ⟨25752375114867109235308133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17168250076578072823538755 25752375114867109235308133)
                ·
                  refine ⟨4828570334037582981620275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25752375114867109235308133 4828570334037582981620275)
                  ·
                    refine ⟨7242855501056374472430413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4828570334037582981620275 7242855501056374472430413)
                    ·
                      refine ⟨2716070812896140427161405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7242855501056374472430413 2716070812896140427161405)
                      ·
                        rfl

theorem cell23_5289529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 2, 1, 4, 1, 3].length) (baseStart_5289529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5289529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5289529 prefixEnd_5289529 := by exact prefixLift 5289529
  have htrace : WordTrace (prefixWord ++ tailWord_5289529) baseStart_5289529 baseEnd_5289529 := by
    simpa [prefixWord, tailWord_5289529, baseEnd_5289529] using wordTrace_append hprefix tailTrace_5289529
  have hstable : (prefixWord ++ tailWord_5289529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5289529).length < 2 ^ (prefixWord ++ tailWord_5289529).sum := by decide
  have hdescent : baseEnd_5289529 < baseStart_5289529 := by decide
  rcases family_descends (prefixWord ++ tailWord_5289529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5289545 : List Nat := [1, 2, 1, 1, 2, 2, 1, 5, 2, 6]
def baseStart_5289545 : Nat := 118140960795 + 5289545 * 2 ^ 59
def prefixEnd_5289545 : Nat := 4983230072969 + 3 ^ 40 * 5289545 * 2
def baseEnd_5289545 : Nat := 905359676195537454853777

theorem tailTrace_5289545 : CollatzResearch.WordTrace tailWord_5289545 prefixEnd_5289545 905359676195537454853777 := by
  unfold tailWord_5289545
  simp only [CollatzResearch.WordTrace]
  refine ⟨192925555621889322209166089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128617037081259548139444059 192925555621889322209166089)
  ·
    refine ⟨144694166716416991656874567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192925555621889322209166089 144694166716416991656874567)
    ·
      refine ⟨217041250074625487485311851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144694166716416991656874567 217041250074625487485311851)
      ·
        refine ⟨325561875111938231227967777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 217041250074625487485311851 325561875111938231227967777)
        ·
          refine ⟨244171406333953673420975833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 325561875111938231227967777 244171406333953673420975833)
          ·
            refine ⟨183128554750465255065731875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 244171406333953673420975833 183128554750465255065731875)
            ·
              refine ⟨274692832125697882598597813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 183128554750465255065731875 274692832125697882598597813)
              ·
                refine ⟨25752453011784176493618545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 274692832125697882598597813 25752453011784176493618545)
                ·
                  refine ⟨19314339758838132370213909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25752453011784176493618545 19314339758838132370213909)
                  ·
                    refine ⟨905359676195537454853777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19314339758838132370213909 905359676195537454853777)
                    ·
                      rfl

theorem cell23_5289545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 5, 2, 6].length) (baseStart_5289545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5289545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5289545 prefixEnd_5289545 := by exact prefixLift 5289545
  have htrace : WordTrace (prefixWord ++ tailWord_5289545) baseStart_5289545 baseEnd_5289545 := by
    simpa [prefixWord, tailWord_5289545, baseEnd_5289545] using wordTrace_append hprefix tailTrace_5289545
  have hstable : (prefixWord ++ tailWord_5289545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5289545).length < 2 ^ (prefixWord ++ tailWord_5289545).sum := by decide
  have hdescent : baseEnd_5289545 < baseStart_5289545 := by decide
  rcases family_descends (prefixWord ++ tailWord_5289545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5289569 : List Nat := [1, 2, 3, 1, 1, 3, 3, 2, 1, 4, 2]
def baseStart_5289569 : Nat := 118140960795 + 5289569 * 2 ^ 59
def prefixEnd_5289569 : Nat := 4983230072969 + 3 ^ 40 * 5289569 * 2
def baseEnd_5289569 : Nat := 2716091352122320270661221

theorem tailTrace_5289569 : CollatzResearch.WordTrace tailWord_5289569 prefixEnd_5289569 2716091352122320270661221 := by
  unfold tailWord_5289569
  simp only [CollatzResearch.WordTrace]
  refine ⟨192926430973802374308039761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128617620649201582872026507 192926430973802374308039761)
  ·
    refine ⟨144694823230351780731029821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192926430973802374308039761 144694823230351780731029821)
    ·
      refine ⟨54260558711381917774136183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 144694823230351780731029821 54260558711381917774136183)
      ·
        refine ⟨81390838067072876661204275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54260558711381917774136183 81390838067072876661204275)
        ·
          refine ⟨122086257100609314991806413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81390838067072876661204275 122086257100609314991806413)
          ·
            refine ⟨45782346412728493121927405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 122086257100609314991806413 45782346412728493121927405)
            ·
              refine ⟨17168379904773184920722777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45782346412728493121927405 17168379904773184920722777)
              ·
                refine ⟨12876284928579888690542083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17168379904773184920722777 12876284928579888690542083)
                ·
                  refine ⟨19314427392869833035813125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12876284928579888690542083 19314427392869833035813125)
                  ·
                    refine ⟨3621455136163093694214961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19314427392869833035813125 3621455136163093694214961)
                    ·
                      refine ⟨2716091352122320270661221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3621455136163093694214961 2716091352122320270661221)
                      ·
                        rfl

theorem cell23_5289569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 3, 2, 1, 4, 2].length) (baseStart_5289569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5289569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5289569 prefixEnd_5289569 := by exact prefixLift 5289569
  have htrace : WordTrace (prefixWord ++ tailWord_5289569) baseStart_5289569 baseEnd_5289569 := by
    simpa [prefixWord, tailWord_5289569, baseEnd_5289569] using wordTrace_append hprefix tailTrace_5289569
  have hstable : (prefixWord ++ tailWord_5289569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5289569).length < 2 ^ (prefixWord ++ tailWord_5289569).sum := by decide
  have hdescent : baseEnd_5289569 < baseStart_5289569 := by decide
  rcases family_descends (prefixWord ++ tailWord_5289569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5289572 : List Nat := [2, 3, 1, 1, 2, 3, 2, 1, 2, 1, 5]
def baseStart_5289572 : Nat := 118140960795 + 5289572 * 2 ^ 59
def prefixEnd_5289572 : Nat := 4983230072969 + 3 ^ 40 * 5289572 * 2
def baseEnd_5289572 : Nat := 2716092892564283758923707

theorem tailTrace_5289572 : CollatzResearch.WordTrace tailWord_5289572 prefixEnd_5289572 2716092892564283758923707 := by
  unfold tailWord_5289572
  simp only [CollatzResearch.WordTrace]
  refine ⟨96463270196395752910199485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128617693595194337213599313 96463270196395752910199485)
  ·
    refine ⟨36173726323648407341324807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96463270196395752910199485 36173726323648407341324807)
    ·
      refine ⟨54260589485472611011987211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36173726323648407341324807 54260589485472611011987211)
      ·
        refine ⟨81390884228208916517980817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54260589485472611011987211 81390884228208916517980817)
        ·
          refine ⟨61043163171156687388485613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81390884228208916517980817 61043163171156687388485613)
          ·
            refine ⟨22891186189183757770682105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61043163171156687388485613 22891186189183757770682105)
            ·
              refine ⟨17168389641887818328011579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22891186189183757770682105 17168389641887818328011579)
              ·
                refine ⟨25752584462831727492017369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17168389641887818328011579 25752584462831727492017369)
                ·
                  refine ⟨19314438347123795619013027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25752584462831727492017369 19314438347123795619013027)
                  ·
                    refine ⟨28971657520685693428519541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19314438347123795619013027 28971657520685693428519541)
                    ·
                      refine ⟨2716092892564283758923707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28971657520685693428519541 2716092892564283758923707)
                      ·
                        rfl

theorem cell23_5289572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 2, 1, 2, 1, 5].length) (baseStart_5289572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5289572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5289572 prefixEnd_5289572 := by exact prefixLift 5289572
  have htrace : WordTrace (prefixWord ++ tailWord_5289572) baseStart_5289572 baseEnd_5289572 := by
    simpa [prefixWord, tailWord_5289572, baseEnd_5289572] using wordTrace_append hprefix tailTrace_5289572
  have hstable : (prefixWord ++ tailWord_5289572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5289572).length < 2 ^ (prefixWord ++ tailWord_5289572).sum := by decide
  have hdescent : baseEnd_5289572 < baseStart_5289572 := by decide
  rcases family_descends (prefixWord ++ tailWord_5289572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5289573 : List Nat := [1, 3, 1, 3, 3, 2, 3, 1, 1, 3, 2]
def baseStart_5289573 : Nat := 118140960795 + 5289573 * 2 ^ 59
def prefixEnd_5289573 : Nat := 4983230072969 + 3 ^ 40 * 5289573 * 2
def baseEnd_5289573 : Nat := 2716093406044938255011203

theorem tailTrace_5289573 : CollatzResearch.WordTrace tailWord_5289573 prefixEnd_5289573 2716093406044938255011203 := by
  unfold tailWord_5289573
  simp only [CollatzResearch.WordTrace]
  refine ⟨192926576865787882991185373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128617717910525255327456915 192926576865787882991185373)
  ·
    refine ⟨72347466324670456121694515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 192926576865787882991185373 72347466324670456121694515)
    ·
      refine ⟨108521199487005684182541773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72347466324670456121694515 108521199487005684182541773)
      ·
        refine ⟨40695449807627131568453165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 108521199487005684182541773 40695449807627131568453165)
        ·
          refine ⟨15260793677860174338169937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40695449807627131568453165 15260793677860174338169937)
          ·
            refine ⟨11445595258395130753627453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15260793677860174338169937 11445595258395130753627453)
            ·
              refine ⟨4292098221898174032610295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11445595258395130753627453 4292098221898174032610295)
              ·
                refine ⟨6438147332847261048915443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4292098221898174032610295 6438147332847261048915443)
                ·
                  refine ⟨9657220999270891573373165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6438147332847261048915443 9657220999270891573373165)
                  ·
                    refine ⟨3621457874726584340014937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9657220999270891573373165 3621457874726584340014937)
                    ·
                      refine ⟨2716093406044938255011203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3621457874726584340014937 2716093406044938255011203)
                      ·
                        rfl

theorem cell23_5289573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 3, 1, 1, 3, 2].length) (baseStart_5289573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5289573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5289573 prefixEnd_5289573 := by exact prefixLift 5289573
  have htrace : WordTrace (prefixWord ++ tailWord_5289573) baseStart_5289573 baseEnd_5289573 := by
    simpa [prefixWord, tailWord_5289573, baseEnd_5289573] using wordTrace_append hprefix tailTrace_5289573
  have hstable : (prefixWord ++ tailWord_5289573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5289573).length < 2 ^ (prefixWord ++ tailWord_5289573).sum := by decide
  have hdescent : baseEnd_5289573 < baseStart_5289573 := by decide
  rcases family_descends (prefixWord ++ tailWord_5289573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5289585 : List Nat := [1, 2, 2, 2, 1, 1, 1, 3, 1, 2, 7]
def baseStart_5289585 : Nat := 118140960795 + 5289585 * 2 ^ 59
def prefixEnd_5289585 : Nat := 4983230072969 + 3 ^ 40 * 5289585 * 2
def baseEnd_5289585 : Nat := 2716099567812792208061147

theorem tailTrace_5289585 : CollatzResearch.WordTrace tailWord_5289585 prefixEnd_5289585 2716099567812792208061147 := by
  unfold tailWord_5289585
  simp only [CollatzResearch.WordTrace]
  refine ⟨192927014541744409040622209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128618009694496272693748139 192927014541744409040622209)
  ·
    refine ⟨144695260906308306780466657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192927014541744409040622209 144695260906308306780466657)
    ·
      refine ⟨108521445679731230085349993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144695260906308306780466657 108521445679731230085349993)
      ·
        refine ⟨81391084259798422564012495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108521445679731230085349993 81391084259798422564012495)
        ·
          refine ⟨122086626389697633846018743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81391084259798422564012495 122086626389697633846018743)
          ·
            refine ⟨183129939584546450769028115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122086626389697633846018743 183129939584546450769028115)
            ·
              refine ⟨274694909376819676153542173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 183129939584546450769028115 274694909376819676153542173)
              ·
                refine ⟨103010591016307378557578315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 274694909376819676153542173 103010591016307378557578315)
                ·
                  refine ⟨154515886524461067836367473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 103010591016307378557578315 154515886524461067836367473)
                  ·
                    refine ⟨115886914893345800877275605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 154515886524461067836367473 115886914893345800877275605)
                    ·
                      refine ⟨2716099567812792208061147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 115886914893345800877275605 2716099567812792208061147)
                      ·
                        rfl

theorem cell23_5289585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 3, 1, 2, 7].length) (baseStart_5289585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5289585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5289585 prefixEnd_5289585 := by exact prefixLift 5289585
  have htrace : WordTrace (prefixWord ++ tailWord_5289585) baseStart_5289585 baseEnd_5289585 := by
    simpa [prefixWord, tailWord_5289585, baseEnd_5289585] using wordTrace_append hprefix tailTrace_5289585
  have hstable : (prefixWord ++ tailWord_5289585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5289585).length < 2 ^ (prefixWord ++ tailWord_5289585).sum := by decide
  have hdescent : baseEnd_5289585 < baseStart_5289585 := by decide
  rcases family_descends (prefixWord ++ tailWord_5289585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5289589 : List Nat := [1, 3, 4, 2, 1, 1, 1, 1, 2, 4, 3]
def baseStart_5289589 : Nat := 118140960795 + 5289589 * 2 ^ 59
def prefixEnd_5289589 : Nat := 4983230072969 + 3 ^ 40 * 5289589 * 2
def baseEnd_5289589 : Nat := 2716101621735410192411129

theorem tailTrace_5289589 : CollatzResearch.WordTrace tailWord_5289589 prefixEnd_5289589 2716101621735410192411129 := by
  unfold tailWord_5289589
  simp only [CollatzResearch.WordTrace]
  refine ⟨192927160433729917723767821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128618106955819945149178547 192927160433729917723767821)
  ·
    refine ⟨72347685162648719146412933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 192927160433729917723767821 72347685162648719146412933)
    ·
      refine ⟨13565190967996634839952425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 72347685162648719146412933 13565190967996634839952425)
      ·
        refine ⟨10173893225997476129964319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13565190967996634839952425 10173893225997476129964319)
        ·
          refine ⟨15260839838996214194946479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10173893225997476129964319 15260839838996214194946479)
          ·
            refine ⟨22891259758494321292419719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15260839838996214194946479 22891259758494321292419719)
            ·
              refine ⟨34336889637741481938629579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22891259758494321292419719 34336889637741481938629579)
              ·
                refine ⟨51505334456612222907944369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34336889637741481938629579 51505334456612222907944369)
                ·
                  refine ⟨38629000842459167180958277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51505334456612222907944369 38629000842459167180958277)
                  ·
                    refine ⟨7242937657961093846429677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 38629000842459167180958277 7242937657961093846429677)
                    ·
                      refine ⟨2716101621735410192411129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7242937657961093846429677 2716101621735410192411129)
                      ·
                        rfl

theorem cell23_5289589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 1, 2, 4, 3].length) (baseStart_5289589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5289589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5289589 prefixEnd_5289589 := by exact prefixLift 5289589
  have htrace : WordTrace (prefixWord ++ tailWord_5289589) baseStart_5289589 baseEnd_5289589 := by
    simpa [prefixWord, tailWord_5289589, baseEnd_5289589] using wordTrace_append hprefix tailTrace_5289589
  have hstable : (prefixWord ++ tailWord_5289589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5289589).length < 2 ^ (prefixWord ++ tailWord_5289589).sum := by decide
  have hdescent : baseEnd_5289589 < baseStart_5289589 := by decide
  rcases family_descends (prefixWord ++ tailWord_5289589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5289672 : List Nat := [2, 1, 3, 1, 2, 2, 1, 1, 2, 4, 4]
def baseStart_5289672 : Nat := 118140960795 + 5289672 * 2 ^ 59
def prefixEnd_5289672 : Nat := 4983230072969 + 3 ^ 40 * 5289672 * 2
def baseEnd_5289672 : Nat := 2716144240629733367673247

theorem tailTrace_5289672 : CollatzResearch.WordTrace tailWord_5289672 prefixEnd_5289672 2716144240629733367673247 := by
  unfold tailWord_5289672
  simp only [CollatzResearch.WordTrace]
  refine ⟨96465093846214611449519635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128620125128286148599359513 96465093846214611449519635)
  ·
    refine ⟨144697640769321917174279453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96465093846214611449519635 144697640769321917174279453)
    ·
      refine ⟨54261615288495718940354795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 144697640769321917174279453 54261615288495718940354795)
      ·
        refine ⟨81392422932743578410532193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54261615288495718940354795 81392422932743578410532193)
        ·
          refine ⟨61044317199557683807899145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81392422932743578410532193 61044317199557683807899145)
          ·
            refine ⟨45783237899668262855924359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61044317199557683807899145 45783237899668262855924359)
            ·
              refine ⟨68674856849502394283886539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45783237899668262855924359 68674856849502394283886539)
              ·
                refine ⟨103012285274253591425829809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68674856849502394283886539 103012285274253591425829809)
                ·
                  refine ⟨77259213955690193569372357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 103012285274253591425829809 77259213955690193569372357)
                  ·
                    refine ⟨14486102616691911294257317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 77259213955690193569372357 14486102616691911294257317)
                    ·
                      refine ⟨2716144240629733367673247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14486102616691911294257317 2716144240629733367673247)
                      ·
                        rfl

theorem cell23_5289672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 1, 2, 4, 4].length) (baseStart_5289672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5289672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5289672 prefixEnd_5289672 := by exact prefixLift 5289672
  have htrace : WordTrace (prefixWord ++ tailWord_5289672) baseStart_5289672 baseEnd_5289672 := by
    simpa [prefixWord, tailWord_5289672, baseEnd_5289672] using wordTrace_append hprefix tailTrace_5289672
  have hstable : (prefixWord ++ tailWord_5289672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5289672).length < 2 ^ (prefixWord ++ tailWord_5289672).sum := by decide
  have hdescent : baseEnd_5289672 < baseStart_5289672 := by decide
  rcases family_descends (prefixWord ++ tailWord_5289672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5289693 : List Nat := [1, 4, 3, 3, 1, 1, 1, 2, 2, 1, 4]
def baseStart_5289693 : Nat := 118140960795 + 5289693 * 2 ^ 59
def prefixEnd_5289693 : Nat := 4983230072969 + 3 ^ 40 * 5289693 * 2
def baseEnd_5289693 : Nat := 2716155023723477785510651

theorem tailTrace_5289693 : CollatzResearch.WordTrace tailWord_5289693 prefixEnd_5289693 2716155023723477785510651 := by
  unfold tailWord_5289693
  simp only [CollatzResearch.WordTrace]
  refine ⟨192930953625353143485553733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128620635750235428990369155 192930953625353143485553733)
  ·
    refine ⟨36174553804753714403541325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 192930953625353143485553733 36174553804753714403541325)
    ·
      refine ⟨13565457676782642901327997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36174553804753714403541325 13565457676782642901327997)
      ·
        refine ⟨5087046628793491087997999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13565457676782642901327997 5087046628793491087997999)
        ·
          refine ⟨7630569943190236631996999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5087046628793491087997999 7630569943190236631996999)
          ·
            refine ⟨11445854914785354947995499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7630569943190236631996999 11445854914785354947995499)
            ·
              refine ⟨17168782372178032421993249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11445854914785354947995499 17168782372178032421993249)
              ·
                refine ⟨12876586779133524316494937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17168782372178032421993249 12876586779133524316494937)
                ·
                  refine ⟨9657440084350143237371203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12876586779133524316494937 9657440084350143237371203)
                  ·
                    refine ⟨14486160126525214856056805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9657440084350143237371203 14486160126525214856056805)
                    ·
                      refine ⟨2716155023723477785510651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14486160126525214856056805 2716155023723477785510651)
                      ·
                        rfl

theorem cell23_5289693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 1, 2, 2, 1, 4].length) (baseStart_5289693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5289693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5289693 prefixEnd_5289693 := by exact prefixLift 5289693
  have htrace : WordTrace (prefixWord ++ tailWord_5289693) baseStart_5289693 baseEnd_5289693 := by
    simpa [prefixWord, tailWord_5289693, baseEnd_5289693] using wordTrace_append hprefix tailTrace_5289693
  have hstable : (prefixWord ++ tailWord_5289693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5289693).length < 2 ^ (prefixWord ++ tailWord_5289693).sum := by decide
  have hdescent : baseEnd_5289693 < baseStart_5289693 := by decide
  rcases family_descends (prefixWord ++ tailWord_5289693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5289719 : List Nat := [1, 1, 3, 1, 1, 1, 4, 1, 3, 5, 2]
def baseStart_5289719 : Nat := 118140960795 + 5289719 * 2 ^ 59
def prefixEnd_5289719 : Nat := 4983230072969 + 3 ^ 40 * 5289719 * 2
def baseEnd_5289719 : Nat := 2716168374220494683785531

theorem tailTrace_5289719 : CollatzResearch.WordTrace tailWord_5289719 prefixEnd_5289719 2716168374220494683785531 := by
  unfold tailWord_5289719
  simp only [CollatzResearch.WordTrace]
  refine ⟨192931901923258949926000211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128621267948839299950666807 192931901923258949926000211)
  ·
    refine ⟨289397852884888424889000317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192931901923258949926000211 289397852884888424889000317)
    ·
      refine ⟨108524194831833159333375119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 289397852884888424889000317 108524194831833159333375119)
      ·
        refine ⟨162786292247749739000062679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108524194831833159333375119 162786292247749739000062679)
        ·
          refine ⟨244179438371624608500094019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162786292247749739000062679 244179438371624608500094019)
          ·
            refine ⟨366269157557436912750141029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 244179438371624608500094019 366269157557436912750141029)
            ·
              refine ⟨68675467042019421140651443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 366269157557436912750141029 68675467042019421140651443)
              ·
                refine ⟨103013200563029131710977165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68675467042019421140651443 103013200563029131710977165)
                ·
                  refine ⟨38629950211135924391616437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 103013200563029131710977165 38629950211135924391616437)
                  ·
                    refine ⟨3621557832293992911714041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 38629950211135924391616437 3621557832293992911714041)
                    ·
                      refine ⟨2716168374220494683785531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3621557832293992911714041 2716168374220494683785531)
                      ·
                        rfl

theorem cell23_5289719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 1, 3, 5, 2].length) (baseStart_5289719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5289719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5289719 prefixEnd_5289719 := by exact prefixLift 5289719
  have htrace : WordTrace (prefixWord ++ tailWord_5289719) baseStart_5289719 baseEnd_5289719 := by
    simpa [prefixWord, tailWord_5289719, baseEnd_5289719] using wordTrace_append hprefix tailTrace_5289719
  have hstable : (prefixWord ++ tailWord_5289719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5289719).length < 2 ^ (prefixWord ++ tailWord_5289719).sum := by decide
  have hdescent : baseEnd_5289719 < baseStart_5289719 := by decide
  rcases family_descends (prefixWord ++ tailWord_5289719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5289786 : List Nat := [3, 1, 1, 1, 5, 1, 2, 1, 3, 2, 3]
def baseStart_5289786 : Nat := 118140960795 + 5289786 * 2 ^ 59
def prefixEnd_5289786 : Nat := 4983230072969 + 3 ^ 40 * 5289786 * 2
def baseEnd_5289786 : Nat := 2716202777424345921647723

theorem tailTrace_5289786 : CollatzResearch.WordTrace tailWord_5289786 prefixEnd_5289786 2716202777424345921647723 := by
  unfold tailWord_5289786
  simp only [CollatzResearch.WordTrace]
  refine ⟨48233586403504055092172303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128622897076010813579126141 48233586403504055092172303)
  ·
    refine ⟨72350379605256082638258455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48233586403504055092172303 72350379605256082638258455)
    ·
      refine ⟨108525569407884123957387683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72350379605256082638258455 108525569407884123957387683)
      ·
        refine ⟨162788354111826185936081525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108525569407884123957387683 162788354111826185936081525)
        ·
          refine ⟨15261408197983704931507643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 162788354111826185936081525 15261408197983704931507643)
          ·
            refine ⟨22892112296975557397261465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15261408197983704931507643 22892112296975557397261465)
            ·
              refine ⟨17169084222731668047946099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22892112296975557397261465 17169084222731668047946099)
              ·
                refine ⟨25753626334097502071919149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17169084222731668047946099 25753626334097502071919149)
                ·
                  refine ⟨9657609875286563276969681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25753626334097502071919149 9657609875286563276969681)
                  ·
                    refine ⟨7243207406464922457727261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9657609875286563276969681 7243207406464922457727261)
                    ·
                      refine ⟨2716202777424345921647723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7243207406464922457727261 2716202777424345921647723)
                      ·
                        rfl

theorem cell23_5289786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 2, 1, 3, 2, 3].length) (baseStart_5289786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5289786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5289786 prefixEnd_5289786 := by exact prefixLift 5289786
  have htrace : WordTrace (prefixWord ++ tailWord_5289786) baseStart_5289786 baseEnd_5289786 := by
    simpa [prefixWord, tailWord_5289786, baseEnd_5289786] using wordTrace_append hprefix tailTrace_5289786
  have hstable : (prefixWord ++ tailWord_5289786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5289786).length < 2 ^ (prefixWord ++ tailWord_5289786).sum := by decide
  have hdescent : baseEnd_5289786 < baseStart_5289786 := by decide
  rcases family_descends (prefixWord ++ tailWord_5289786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5289800 : List Nat := [2, 1, 3, 1, 1, 4, 1, 5, 1, 2, 2]
def baseStart_5289800 : Nat := 118140960795 + 5289800 * 2 ^ 59
def prefixEnd_5289800 : Nat := 4983230072969 + 3 ^ 40 * 5289800 * 2
def baseEnd_5289800 : Nat := 2716209966153508866872659

theorem tailTrace_5289800 : CollatzResearch.WordTrace tailWord_5289800 prefixEnd_5289800 2716209966153508866872659 := by
  unfold tailWord_5289800
  simp only [CollatzResearch.WordTrace]
  refine ⟨96467428117982750379849427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128623237490643667173132569 96467428117982750379849427)
  ·
    refine ⟨144701142176974125569774141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96467428117982750379849427 144701142176974125569774141)
    ·
      refine ⟨54262928316365297088665303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 144701142176974125569774141 54262928316365297088665303)
      ·
        refine ⟨81394392474547945632997955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54262928316365297088665303 81394392474547945632997955)
        ·
          refine ⟨122091588711821918449496933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81394392474547945632997955 122091588711821918449496933)
          ·
            refine ⟨22892172883466609709280675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 122091588711821918449496933 22892172883466609709280675)
            ·
              refine ⟨34338259325199914563921013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22892172883466609709280675 34338259325199914563921013)
              ·
                refine ⟨3219211811737491990367595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34338259325199914563921013 3219211811737491990367595)
                ·
                  refine ⟨4828817717606237985551393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3219211811737491990367595 4828817717606237985551393)
                  ·
                    refine ⟨3621613288204678489163545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4828817717606237985551393 3621613288204678489163545)
                    ·
                      refine ⟨2716209966153508866872659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3621613288204678489163545 2716209966153508866872659)
                      ·
                        rfl

theorem cell23_5289800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 5, 1, 2, 2].length) (baseStart_5289800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5289800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5289800 prefixEnd_5289800 := by exact prefixLift 5289800
  have htrace : WordTrace (prefixWord ++ tailWord_5289800) baseStart_5289800 baseEnd_5289800 := by
    simpa [prefixWord, tailWord_5289800, baseEnd_5289800] using wordTrace_append hprefix tailTrace_5289800
  have hstable : (prefixWord ++ tailWord_5289800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5289800).length < 2 ^ (prefixWord ++ tailWord_5289800).sum := by decide
  have hdescent : baseEnd_5289800 < baseStart_5289800 := by decide
  rcases family_descends (prefixWord ++ tailWord_5289800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5289856 : List Nat := [2, 1, 1, 2, 1, 2, 4, 1, 3, 4, 2]
def baseStart_5289856 : Nat := 118140960795 + 5289856 * 2 ^ 59
def prefixEnd_5289856 : Nat := 4983230072969 + 3 ^ 40 * 5289856 * 2
def baseEnd_5289856 : Nat := 2716238721070160647772401

theorem tailTrace_5289856 : CollatzResearch.WordTrace tailWord_5289856 prefixEnd_5289856 2716238721070160647772401 := by
  unfold tailWord_5289856
  simp only [CollatzResearch.WordTrace]
  refine ⟨96468449361881311161868711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128624599149175081549158281 96468449361881311161868711)
  ·
    refine ⟨144702674042821966742803067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96468449361881311161868711 144702674042821966742803067)
    ·
      refine ⟨217054011064232950114204601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144702674042821966742803067 217054011064232950114204601)
      ·
        refine ⟨162790508298174712585653451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 217054011064232950114204601 162790508298174712585653451)
        ·
          refine ⟨244185762447262068878480177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162790508298174712585653451 244185762447262068878480177)
          ·
            refine ⟨183139321835446551658860133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 244185762447262068878480177 183139321835446551658860133)
            ·
              refine ⟨34338622844146228436036275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 183139321835446551658860133 34338622844146228436036275)
              ·
                refine ⟨51507934266219342654054413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34338622844146228436036275 51507934266219342654054413)
                ·
                  refine ⟨19315475349832253495270405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51507934266219342654054413 19315475349832253495270405)
                  ·
                    refine ⟨3621651628093547530363201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19315475349832253495270405 3621651628093547530363201)
                    ·
                      refine ⟨2716238721070160647772401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3621651628093547530363201 2716238721070160647772401)
                      ·
                        rfl

theorem cell23_5289856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 1, 3, 4, 2].length) (baseStart_5289856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5289856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5289856 prefixEnd_5289856 := by exact prefixLift 5289856
  have htrace : WordTrace (prefixWord ++ tailWord_5289856) baseStart_5289856 baseEnd_5289856 := by
    simpa [prefixWord, tailWord_5289856, baseEnd_5289856] using wordTrace_append hprefix tailTrace_5289856
  have hstable : (prefixWord ++ tailWord_5289856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5289856).length < 2 ^ (prefixWord ++ tailWord_5289856).sum := by decide
  have hdescent : baseEnd_5289856 < baseStart_5289856 := by decide
  rcases family_descends (prefixWord ++ tailWord_5289856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5289859 : List Nat := [1, 1, 1, 3, 4, 2, 1, 1, 1, 3, 5]
def baseStart_5289859 : Nat := 118140960795 + 5289859 * 2 ^ 59
def prefixEnd_5289859 : Nat := 4983230072969 + 3 ^ 40 * 5289859 * 2
def baseEnd_5289859 : Nat := 2716240261512124136034887

theorem tailTrace_5289859 : CollatzResearch.WordTrace tailWord_5289859 prefixEnd_5289859 2716240261512124136034887 := by
  unfold tailWord_5289859
  simp only [CollatzResearch.WordTrace]
  refine ⟨192937008142751753836096631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128624672095167835890731087 192937008142751753836096631)
  ·
    refine ⟨289405512214127630754144947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192937008142751753836096631 289405512214127630754144947)
    ·
      refine ⟨434108268321191446131217421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 289405512214127630754144947 434108268321191446131217421)
      ·
        refine ⟨162790600620446792299206533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 434108268321191446131217421 162790600620446792299206533)
        ·
          refine ⟨30523237616333773556101225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 162790600620446792299206533 30523237616333773556101225)
          ·
            refine ⟨22892428212250330167075919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30523237616333773556101225 22892428212250330167075919)
            ·
              refine ⟨34338642318375495250613879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22892428212250330167075919 34338642318375495250613879)
              ·
                refine ⟨51507963477563242875920819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34338642318375495250613879 51507963477563242875920819)
                ·
                  refine ⟨77261945216344864313881229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51507963477563242875920819 77261945216344864313881229)
                  ·
                    refine ⟨28973229456129324117705461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 77261945216344864313881229 28973229456129324117705461)
                    ·
                      refine ⟨2716240261512124136034887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28973229456129324117705461 2716240261512124136034887)
                      ·
                        rfl

theorem cell23_5289859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 1, 1, 3, 5].length) (baseStart_5289859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5289859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5289859 prefixEnd_5289859 := by exact prefixLift 5289859
  have htrace : WordTrace (prefixWord ++ tailWord_5289859) baseStart_5289859 baseEnd_5289859 := by
    simpa [prefixWord, tailWord_5289859, baseEnd_5289859] using wordTrace_append hprefix tailTrace_5289859
  have hstable : (prefixWord ++ tailWord_5289859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5289859).length < 2 ^ (prefixWord ++ tailWord_5289859).sum := by decide
  have hdescent : baseEnd_5289859 < baseStart_5289859 := by decide
  rcases family_descends (prefixWord ++ tailWord_5289859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5289873 : List Nat := [1, 2, 2, 1, 1, 1, 6, 1, 4, 2, 2]
def baseStart_5289873 : Nat := 118140960795 + 5289873 * 2 ^ 59
def prefixEnd_5289873 : Nat := 4983230072969 + 3 ^ 40 * 5289873 * 2
def baseEnd_5289873 : Nat := 2716247450241287081259823

theorem tailTrace_5289873 : CollatzResearch.WordTrace tailWord_5289873 prefixEnd_5289873 2716247450241287081259823 := by
  unfold tailWord_5289873
  simp only [CollatzResearch.WordTrace]
  refine ⟨192937518764701034227106273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128625012509800689484737515 192937518764701034227106273)
  ·
    refine ⟨144703139073525775670329705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192937518764701034227106273 144703139073525775670329705)
    ·
      refine ⟨108527354305144331752747279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144703139073525775670329705 108527354305144331752747279)
      ·
        refine ⟨162791031457716497629120919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108527354305144331752747279 162791031457716497629120919)
        ·
          refine ⟨244186547186574746443681379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162791031457716497629120919 244186547186574746443681379)
          ·
            refine ⟨366279820779862119665522069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 244186547186574746443681379 366279820779862119665522069)
            ·
              refine ⟨17169366599056036859321347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 366279820779862119665522069 17169366599056036859321347)
              ·
                refine ⟨25754049898584055288982021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17169366599056036859321347 25754049898584055288982021)
                ·
                  refine ⟨4828884355984510366684129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25754049898584055288982021 4828884355984510366684129)
                  ·
                    refine ⟨3621663266988382775013097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4828884355984510366684129 3621663266988382775013097)
                    ·
                      refine ⟨2716247450241287081259823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3621663266988382775013097 2716247450241287081259823)
                      ·
                        rfl

theorem cell23_5289873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 6, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 6, 1, 4, 2, 2].length) (baseStart_5289873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5289873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5289873 prefixEnd_5289873 := by exact prefixLift 5289873
  have htrace : WordTrace (prefixWord ++ tailWord_5289873) baseStart_5289873 baseEnd_5289873 := by
    simpa [prefixWord, tailWord_5289873, baseEnd_5289873] using wordTrace_append hprefix tailTrace_5289873
  have hstable : (prefixWord ++ tailWord_5289873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5289873).length < 2 ^ (prefixWord ++ tailWord_5289873).sum := by decide
  have hdescent : baseEnd_5289873 < baseStart_5289873 := by decide
  rcases family_descends (prefixWord ++ tailWord_5289873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5289919 : List Nat := [1, 1, 2, 2, 2, 1, 3, 1, 3, 2, 5]
def baseStart_5289919 : Nat := 118140960795 + 5289919 * 2 ^ 59
def prefixEnd_5289919 : Nat := 4983230072969 + 3 ^ 40 * 5289919 * 2
def baseEnd_5289919 : Nat := 2716271070351393901284611

theorem tailTrace_5289919 : CollatzResearch.WordTrace tailWord_5289919 prefixEnd_5289919 2716271070351393901284611 := by
  unfold tailWord_5289919
  simp only [CollatzResearch.WordTrace]
  refine ⟨192939196522534384083280811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128626131015022922722187207 192939196522534384083280811)
  ·
    refine ⟨289408794783801576124921217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192939196522534384083280811 289408794783801576124921217)
    ·
      refine ⟨217056596087851182093690913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 289408794783801576124921217 217056596087851182093690913)
      ·
        refine ⟨162792447065888386570268185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 217056596087851182093690913 162792447065888386570268185)
        ·
          refine ⟨122094335299416289927701139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 162792447065888386570268185 122094335299416289927701139)
          ·
            refine ⟨183141502949124434891551709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122094335299416289927701139 183141502949124434891551709)
            ·
              refine ⟨68678063605921663084331891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 183141502949124434891551709 68678063605921663084331891)
              ·
                refine ⟨103017095408882494626497837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68678063605921663084331891 103017095408882494626497837)
                ·
                  refine ⟨38631410778330935484936689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 103017095408882494626497837 38631410778330935484936689)
                  ·
                    refine ⟨28973558083748201613702517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 38631410778330935484936689 28973558083748201613702517)
                    ·
                      refine ⟨2716271070351393901284611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28973558083748201613702517 2716271070351393901284611)
                      ·
                        rfl

theorem cell23_5289919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 1, 3, 2, 5].length) (baseStart_5289919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5289919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5289919 prefixEnd_5289919 := by exact prefixLift 5289919
  have htrace : WordTrace (prefixWord ++ tailWord_5289919) baseStart_5289919 baseEnd_5289919 := by
    simpa [prefixWord, tailWord_5289919, baseEnd_5289919] using wordTrace_append hprefix tailTrace_5289919
  have hstable : (prefixWord ++ tailWord_5289919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5289919).length < 2 ^ (prefixWord ++ tailWord_5289919).sum := by decide
  have hdescent : baseEnd_5289919 < baseStart_5289919 := by decide
  rcases family_descends (prefixWord ++ tailWord_5289919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5290033 : List Nat := [1, 2, 2, 3, 1, 3, 2, 3, 1, 5]
def baseStart_5290033 : Nat := 118140960795 + 5290033 * 2 ^ 59
def prefixEnd_5290033 : Nat := 4983230072969 + 3 ^ 40 * 5290033 * 2
def baseEnd_5290033 : Nat := 905443202382002151753029

theorem tailTrace_5290033 : CollatzResearch.WordTrace tailWord_5290033 prefixEnd_5290033 905443202382002151753029 := by
  unfold tailWord_5290033
  simp only [CollatzResearch.WordTrace]
  refine ⟨192943354444121381552930753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128628902962747587701953835 192943354444121381552930753)
  ·
    refine ⟨144707515833091036164698065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192943354444121381552930753 144707515833091036164698065)
    ·
      refine ⟨108530636874818277123523549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144707515833091036164698065 108530636874818277123523549)
      ·
        refine ⟨40698988828056853921321331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 108530636874818277123523549 40698988828056853921321331)
        ·
          refine ⟨61048483242085280881981997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40698988828056853921321331 61048483242085280881981997)
          ·
            refine ⟨22893181215781980330743249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61048483242085280881981997 22893181215781980330743249)
            ·
              refine ⟨17169885911836485248057437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22893181215781980330743249 17169885911836485248057437)
              ·
                refine ⟨6438707216938681968021539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17169885911836485248057437 6438707216938681968021539)
                ·
                  refine ⟨9658060825408022952032309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6438707216938681968021539 9658060825408022952032309)
                  ·
                    refine ⟨905443202382002151753029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9658060825408022952032309 905443202382002151753029)
                    ·
                      rfl

theorem cell23_5290033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 2, 3, 1, 5].length) (baseStart_5290033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5290033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5290033 prefixEnd_5290033 := by exact prefixLift 5290033
  have htrace : WordTrace (prefixWord ++ tailWord_5290033) baseStart_5290033 baseEnd_5290033 := by
    simpa [prefixWord, tailWord_5290033, baseEnd_5290033] using wordTrace_append hprefix tailTrace_5290033
  have hstable : (prefixWord ++ tailWord_5290033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5290033).length < 2 ^ (prefixWord ++ tailWord_5290033).sum := by decide
  have hdescent : baseEnd_5290033 < baseStart_5290033 := by decide
  rcases family_descends (prefixWord ++ tailWord_5290033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5290056 : List Nat := [2, 1, 3, 1, 1, 1, 2, 3, 3, 1, 5]
def baseStart_5290056 : Nat := 118140960795 + 5290056 * 2 ^ 59
def prefixEnd_5290056 : Nat := 4983230072969 + 3 ^ 40 * 5290056 * 2
def baseEnd_5290056 : Nat := 2716341417201059865271481

theorem tailTrace_5290056 : CollatzResearch.WordTrace tailWord_5290056 prefixEnd_5290056 2716341417201059865271481 := by
  unfold tailWord_5290056
  simp only [CollatzResearch.WordTrace]
  refine ⟨96472096661519028240509011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128629462215358704320678681 96472096661519028240509011)
  ·
    refine ⟨144708144992278542360763517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96472096661519028240509011 144708144992278542360763517)
    ·
      refine ⟨54265554372104453385286319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 144708144992278542360763517 54265554372104453385286319)
      ·
        refine ⟨81398331558156680077929479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54265554372104453385286319 81398331558156680077929479)
        ·
          refine ⟨122097497337235020116894219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81398331558156680077929479 122097497337235020116894219)
          ·
            refine ⟨183146246005852530175341329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122097497337235020116894219 183146246005852530175341329)
            ·
              refine ⟨137359684504389397631505997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 183146246005852530175341329 137359684504389397631505997)
              ·
                refine ⟨51509881689146024111814749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 137359684504389397631505997 51509881689146024111814749)
                ·
                  refine ⟨19316205633429759041930531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51509881689146024111814749 19316205633429759041930531)
                  ·
                    refine ⟨28974308450144638562895797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19316205633429759041930531 28974308450144638562895797)
                    ·
                      refine ⟨2716341417201059865271481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28974308450144638562895797 2716341417201059865271481)
                      ·
                        rfl

theorem cell23_5290056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 3, 3, 1, 5].length) (baseStart_5290056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5290056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5290056 prefixEnd_5290056 := by exact prefixLift 5290056
  have htrace : WordTrace (prefixWord ++ tailWord_5290056) baseStart_5290056 baseEnd_5290056 := by
    simpa [prefixWord, tailWord_5290056, baseEnd_5290056] using wordTrace_append hprefix tailTrace_5290056
  have hstable : (prefixWord ++ tailWord_5290056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5290056).length < 2 ^ (prefixWord ++ tailWord_5290056).sum := by decide
  have hdescent : baseEnd_5290056 < baseStart_5290056 := by decide
  rcases family_descends (prefixWord ++ tailWord_5290056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5290063 : List Nat := [1, 1, 2, 1, 1, 2, 2, 7, 2, 4]
def baseStart_5290063 : Nat := 118140960795 + 5290063 * 2 ^ 59
def prefixEnd_5290063 : Nat := 4983230072969 + 3 ^ 40 * 5290063 * 2
def baseEnd_5290063 : Nat := 905448337188547112627983

theorem tailTrace_5290063 : CollatzResearch.WordTrace tailWord_5290063 prefixEnd_5290063 905448337188547112627983 := by
  unfold tailWord_5290063
  simp only [CollatzResearch.WordTrace]
  refine ⟨192944448634012696676522843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128629632422675131117681895 192944448634012696676522843)
  ·
    refine ⟨289416672951019045014784265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192944448634012696676522843 289416672951019045014784265)
    ·
      refine ⟨217062504713264283761088199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 289416672951019045014784265 217062504713264283761088199)
      ·
        refine ⟨325593757069896425641632299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 217062504713264283761088199 325593757069896425641632299)
        ·
          refine ⟨488390635604844638462448449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 325593757069896425641632299 488390635604844638462448449)
          ·
            refine ⟨366292976703633478846836337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 488390635604844638462448449 366292976703633478846836337)
            ·
              refine ⟨274719732527725109135127253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 366292976703633478846836337 274719732527725109135127253)
              ·
                refine ⟨6438743731118557245354545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 274719732527725109135127253 6438743731118557245354545)
                ·
                  refine ⟨4829057798338917934015909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6438743731118557245354545 4829057798338917934015909)
                  ·
                    refine ⟨905448337188547112627983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4829057798338917934015909 905448337188547112627983)
                    ·
                      rfl

theorem cell23_5290063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 7, 2, 4].length) (baseStart_5290063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5290063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5290063 prefixEnd_5290063 := by exact prefixLift 5290063
  have htrace : WordTrace (prefixWord ++ tailWord_5290063) baseStart_5290063 baseEnd_5290063 := by
    simpa [prefixWord, tailWord_5290063, baseEnd_5290063] using wordTrace_append hprefix tailTrace_5290063
  have hstable : (prefixWord ++ tailWord_5290063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5290063).length < 2 ^ (prefixWord ++ tailWord_5290063).sum := by decide
  have hdescent : baseEnd_5290063 < baseStart_5290063 := by decide
  rcases family_descends (prefixWord ++ tailWord_5290063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5290073 : List Nat := [1, 2, 1, 2, 2, 1, 5, 1, 3, 2, 3]
def baseStart_5290073 : Nat := 118140960795 + 5290073 * 2 ^ 59
def prefixEnd_5290073 : Nat := 4983230072969 + 3 ^ 40 * 5290073 * 2
def baseEnd_5290073 : Nat := 2716350146372186298758903

theorem tailTrace_5290073 : CollatzResearch.WordTrace tailWord_5290073 prefixEnd_5290073 2716350146372186298758903 := by
  unfold tailWord_5290073
  simp only [CollatzResearch.WordTrace]
  refine ⟨192944813363976468384386873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128629875575984312256257915 192944813363976468384386873)
  ·
    refine ⟨144708610022982351288290155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192944813363976468384386873 144708610022982351288290155)
    ·
      refine ⟨217062915034473526932435233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144708610022982351288290155 217062915034473526932435233)
      ·
        refine ⟨162797186275855145199326425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 217062915034473526932435233 162797186275855145199326425)
        ·
          refine ⟨122097889706891358899494819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 162797186275855145199326425 122097889706891358899494819)
          ·
            refine ⟨183146834560337038349242229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122097889706891358899494819 183146834560337038349242229)
            ·
              refine ⟨17170015740031597345241459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 183146834560337038349242229 17170015740031597345241459)
              ·
                refine ⟨25755023610047396017862189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17170015740031597345241459 25755023610047396017862189)
                ·
                  refine ⟨9658133853767773506698321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25755023610047396017862189 9658133853767773506698321)
                  ·
                    refine ⟨7243600390325830130023741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9658133853767773506698321 7243600390325830130023741)
                    ·
                      refine ⟨2716350146372186298758903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7243600390325830130023741 2716350146372186298758903)
                      ·
                        rfl

theorem cell23_5290073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 5, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 5, 1, 3, 2, 3].length) (baseStart_5290073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5290073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5290073 prefixEnd_5290073 := by exact prefixLift 5290073
  have htrace : WordTrace (prefixWord ++ tailWord_5290073) baseStart_5290073 baseEnd_5290073 := by
    simpa [prefixWord, tailWord_5290073, baseEnd_5290073] using wordTrace_append hprefix tailTrace_5290073
  have hstable : (prefixWord ++ tailWord_5290073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5290073).length < 2 ^ (prefixWord ++ tailWord_5290073).sum := by decide
  have hdescent : baseEnd_5290073 < baseStart_5290073 := by decide
  rcases family_descends (prefixWord ++ tailWord_5290073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5290120 : List Nat := [2, 1, 3, 4, 1, 1, 1, 3, 1, 3, 3]
def baseStart_5290120 : Nat := 118140960795 + 5290120 * 2 ^ 59
def prefixEnd_5290120 : Nat := 4983230072969 + 3 ^ 40 * 5290120 * 2
def baseEnd_5290120 : Nat := 2716374279962947614871187

theorem tailTrace_5290120 : CollatzResearch.WordTrace tailWord_5290120 prefixEnd_5290120 2716374279962947614871187 := by
  unfold tailWord_5290120
  simp only [CollatzResearch.WordTrace]
  refine ⟨96473263797403097705673907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128631018396537463607565209 96473263797403097705673907)
  ·
    refine ⟨144709895696104646558510861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96473263797403097705673907 144709895696104646558510861)
    ·
      refine ⟨54266210886039242459441573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 144709895696104646558510861 54266210886039242459441573)
      ·
        refine ⟨10174914541132357961145295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54266210886039242459441573 10174914541132357961145295)
        ·
          refine ⟨15262371811698536941717943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10174914541132357961145295 15262371811698536941717943)
          ·
            refine ⟨22893557717547805412576915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15262371811698536941717943 22893557717547805412576915)
            ·
              refine ⟨34340336576321708118865373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22893557717547805412576915 34340336576321708118865373)
              ·
                refine ⟨12877626216120640544574515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34340336576321708118865373 12877626216120640544574515)
                ·
                  refine ⟨19316439324180960816861773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12877626216120640544574515 19316439324180960816861773)
                  ·
                    refine ⟨7243664746567860306323165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19316439324180960816861773 7243664746567860306323165)
                    ·
                      refine ⟨2716374279962947614871187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7243664746567860306323165 2716374279962947614871187)
                      ·
                        rfl

theorem cell23_5290120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 3, 1, 3, 3].length) (baseStart_5290120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5290120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5290120 prefixEnd_5290120 := by exact prefixLift 5290120
  have htrace : WordTrace (prefixWord ++ tailWord_5290120) baseStart_5290120 baseEnd_5290120 := by
    simpa [prefixWord, tailWord_5290120, baseEnd_5290120] using wordTrace_append hprefix tailTrace_5290120
  have hstable : (prefixWord ++ tailWord_5290120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5290120).length < 2 ^ (prefixWord ++ tailWord_5290120).sum := by decide
  have hdescent : baseEnd_5290120 < baseStart_5290120 := by decide
  rcases family_descends (prefixWord ++ tailWord_5290120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5290154 : List Nat := [3, 1, 5, 1, 2, 1, 1, 1, 4, 1, 3]
def baseStart_5290154 : Nat := 118140960795 + 5290154 * 2 ^ 59
def prefixEnd_5290154 : Nat := 4983230072969 + 3 ^ 40 * 5290154 * 2
def baseEnd_5290154 : Nat := 2716391738305200481846031

theorem tailTrace_5290154 : CollatzResearch.WordTrace tailWord_5290154 prefixEnd_5290154 2716391738305200481846031 := by
  unfold tailWord_5290154
  simp only [CollatzResearch.WordTrace]
  refine ⟨48236941919170754804521379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128631845117788679478723677 48236941919170754804521379)
  ·
    refine ⟨72355412878756132206782069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48236941919170754804521379 72355412878756132206782069)
    ·
      refine ⟨6783319957383387394385819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 72355412878756132206782069 6783319957383387394385819)
      ·
        refine ⟨10174979936075081091578729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6783319957383387394385819 10174979936075081091578729)
        ·
          refine ⟨7631234952056310818684047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10174979936075081091578729 7631234952056310818684047)
          ·
            refine ⟨11446852428084466228026071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7631234952056310818684047 11446852428084466228026071)
            ·
              refine ⟨17170278642126699342039107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11446852428084466228026071 17170278642126699342039107)
              ·
                refine ⟨25755417963190049013058661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17170278642126699342039107 25755417963190049013058661)
                ·
                  refine ⟨4829140868098134189948499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25755417963190049013058661 4829140868098134189948499)
                  ·
                    refine ⟨7243711302147201284922749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4829140868098134189948499 7243711302147201284922749)
                    ·
                      refine ⟨2716391738305200481846031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7243711302147201284922749 2716391738305200481846031)
                      ·
                        rfl

theorem cell23_5290154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 1, 1, 4, 1, 3].length) (baseStart_5290154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5290154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5290154 prefixEnd_5290154 := by exact prefixLift 5290154
  have htrace : WordTrace (prefixWord ++ tailWord_5290154) baseStart_5290154 baseEnd_5290154 := by
    simpa [prefixWord, tailWord_5290154, baseEnd_5290154] using wordTrace_append hprefix tailTrace_5290154
  have hstable : (prefixWord ++ tailWord_5290154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5290154).length < 2 ^ (prefixWord ++ tailWord_5290154).sum := by decide
  have hdescent : baseEnd_5290154 < baseStart_5290154 := by decide
  rcases family_descends (prefixWord ++ tailWord_5290154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5290193 : List Nat := [1, 2, 2, 1, 2, 2, 2, 2, 1, 5, 3]
def baseStart_5290193 : Nat := 118140960795 + 5290193 * 2 ^ 59
def prefixEnd_5290193 : Nat := 4983230072969 + 3 ^ 40 * 5290193 * 2
def baseEnd_5290193 : Nat := 2716411764050725829258351

theorem tailTrace_5290193 : CollatzResearch.WordTrace tailWord_5290193 prefixEnd_5290193 2716411764050725829258351 := by
  unfold tailWord_5290193
  simp only [CollatzResearch.WordTrace]
  refine ⟨192949190123541728878755233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128632793415694485919170155 192949190123541728878755233)
  ·
    refine ⟨144711892592656296659066425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192949190123541728878755233 144711892592656296659066425)
    ·
      refine ⟨108533919444492222494299819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144711892592656296659066425 108533919444492222494299819)
      ·
        refine ⟨162800879166738333741449729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108533919444492222494299819 162800879166738333741449729)
        ·
          refine ⟨122100659375053750306087297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 162800879166738333741449729 122100659375053750306087297)
          ·
            refine ⟨91575494531290312729565473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 122100659375053750306087297 91575494531290312729565473)
            ·
              refine ⟨68681620898467734547174105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91575494531290312729565473 68681620898467734547174105)
              ·
                refine ⟨51511215673850800910380579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68681620898467734547174105 51511215673850800910380579)
                ·
                  refine ⟨77266823510776201365570869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51511215673850800910380579 77266823510776201365570869)
                  ·
                    refine ⟨7243764704135268878022269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 77266823510776201365570869 7243764704135268878022269)
                    ·
                      refine ⟨2716411764050725829258351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7243764704135268878022269 2716411764050725829258351)
                      ·
                        rfl

theorem cell23_5290193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 2, 1, 5, 3].length) (baseStart_5290193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5290193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5290193 prefixEnd_5290193 := by exact prefixLift 5290193
  have htrace : WordTrace (prefixWord ++ tailWord_5290193) baseStart_5290193 baseEnd_5290193 := by
    simpa [prefixWord, tailWord_5290193, baseEnd_5290193] using wordTrace_append hprefix tailTrace_5290193
  have hstable : (prefixWord ++ tailWord_5290193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5290193).length < 2 ^ (prefixWord ++ tailWord_5290193).sum := by decide
  have hdescent : baseEnd_5290193 < baseStart_5290193 := by decide
  rcases family_descends (prefixWord ++ tailWord_5290193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5290220 : List Nat := [2, 2, 1, 1, 2, 3, 2, 1, 2, 5, 2]
def baseStart_5290220 : Nat := 118140960795 + 5290220 * 2 ^ 59
def prefixEnd_5290220 : Nat := 4983230072969 + 3 ^ 40 * 5290220 * 2
def baseEnd_5290220 : Nat := 2716425628028397223620727

theorem tailTrace_5290220 : CollatzResearch.WordTrace tailWord_5290220 prefixEnd_5290220 2716425628028397223620727 := by
  unfold tailWord_5290220
  simp only [CollatzResearch.WordTrace]
  refine ⟨96475087447221956244994057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128633449929629274993325409 96475087447221956244994057)
  ·
    refine ⟨72356315585416467183745543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96475087447221956244994057 72356315585416467183745543)
    ·
      refine ⟨108534473378124700775618315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72356315585416467183745543 108534473378124700775618315)
      ·
        refine ⟨162801710067187051163427473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108534473378124700775618315 162801710067187051163427473)
        ·
          refine ⟨122101282550390288372570605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 162801710067187051163427473 122101282550390288372570605)
          ·
            refine ⟨45787980956396358139713977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 122101282550390288372570605 45787980956396358139713977)
            ·
              refine ⟨34340985717297268604785483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45787980956396358139713977 34340985717297268604785483)
              ·
                refine ⟨51511478575945902907178225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34340985717297268604785483 51511478575945902907178225)
                ·
                  refine ⟨38633608931959427180383669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51511478575945902907178225 38633608931959427180383669)
                  ·
                    refine ⟨3621900837371196298160969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 38633608931959427180383669 3621900837371196298160969)
                    ·
                      refine ⟨2716425628028397223620727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3621900837371196298160969 2716425628028397223620727)
                      ·
                        rfl

theorem cell23_5290220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 5, 2].length) (baseStart_5290220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5290220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5290220 prefixEnd_5290220 := by exact prefixLift 5290220
  have htrace : WordTrace (prefixWord ++ tailWord_5290220) baseStart_5290220 baseEnd_5290220 := by
    simpa [prefixWord, tailWord_5290220, baseEnd_5290220] using wordTrace_append hprefix tailTrace_5290220
  have hstable : (prefixWord ++ tailWord_5290220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5290220).length < 2 ^ (prefixWord ++ tailWord_5290220).sum := by decide
  have hdescent : baseEnd_5290220 < baseStart_5290220 := by decide
  rcases family_descends (prefixWord ++ tailWord_5290220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5290223 : List Nat := [1, 1, 2, 1, 6, 1, 1, 1, 1, 1, 7]
def baseStart_5290223 : Nat := 118140960795 + 5290223 * 2 ^ 59
def prefixEnd_5290223 : Nat := 4983230072969 + 3 ^ 40 * 5290223 * 2
def baseEnd_5290223 : Nat := 2716427168470360711883213

theorem tailTrace_5290223 : CollatzResearch.WordTrace tailWord_5290223 prefixEnd_5290223 2716427168470360711883213 := by
  unfold tailWord_5290223
  simp only [CollatzResearch.WordTrace]
  refine ⟨192950284313433044002347323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128633522875622029334898215 192950284313433044002347323)
  ·
    refine ⟨289425426470149566003520985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192950284313433044002347323 289425426470149566003520985)
    ·
      refine ⟨217069069852612174502640739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 289425426470149566003520985 217069069852612174502640739)
      ·
        refine ⟨325603604778918261753961109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 217069069852612174502640739 325603604778918261753961109)
        ·
          refine ⟨15262668974011793519716927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 325603604778918261753961109 15262668974011793519716927)
          ·
            refine ⟨22894003461017690279575391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15262668974011793519716927 22894003461017690279575391)
            ·
              refine ⟨34341005191526535419363087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22894003461017690279575391 34341005191526535419363087)
              ·
                refine ⟨51511507787289803129044631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34341005191526535419363087 51511507787289803129044631)
                ·
                  refine ⟨77267261680934704693566947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51511507787289803129044631 77267261680934704693566947)
                  ·
                    refine ⟨115900892521402057040350421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 77267261680934704693566947 115900892521402057040350421)
                    ·
                      refine ⟨2716427168470360711883213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 115900892521402057040350421 2716427168470360711883213)
                      ·
                        rfl

theorem cell23_5290223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 1, 1, 1, 7].length) (baseStart_5290223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5290223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5290223 prefixEnd_5290223 := by exact prefixLift 5290223
  have htrace : WordTrace (prefixWord ++ tailWord_5290223) baseStart_5290223 baseEnd_5290223 := by
    simpa [prefixWord, tailWord_5290223, baseEnd_5290223] using wordTrace_append hprefix tailTrace_5290223
  have hstable : (prefixWord ++ tailWord_5290223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5290223).length < 2 ^ (prefixWord ++ tailWord_5290223).sum := by decide
  have hdescent : baseEnd_5290223 < baseStart_5290223 := by decide
  rcases family_descends (prefixWord ++ tailWord_5290223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5290233 : List Nat := [1, 2, 1, 3, 1, 1, 2, 4, 1, 3, 4]
def baseStart_5290233 : Nat := 118140960795 + 5290233 * 2 ^ 59
def prefixEnd_5290233 : Nat := 4983230072969 + 3 ^ 40 * 5290233 * 2
def baseEnd_5290233 : Nat := 2716432303276905672758167

theorem tailTrace_5290233 : CollatzResearch.WordTrace tailWord_5290233 prefixEnd_5290233 2716432303276905672758167 := by
  unfold tailWord_5290233
  simp only [CollatzResearch.WordTrace]
  refine ⟨192950649043396815710211353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128633766028931210473474235 192950649043396815710211353)
  ·
    refine ⟨144712986782547611782658515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192950649043396815710211353 144712986782547611782658515)
    ·
      refine ⟨217069480173821417673987773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144712986782547611782658515 217069480173821417673987773)
      ·
        refine ⟨81401055065183031627745415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 217069480173821417673987773 81401055065183031627745415)
        ·
          refine ⟨122101582597774547441618123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81401055065183031627745415 122101582597774547441618123)
          ·
            refine ⟨183152373896661821162427185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122101582597774547441618123 183152373896661821162427185)
            ·
              refine ⟨137364280422496365871820389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 183152373896661821162427185 137364280422496365871820389)
              ·
                refine ⟨25755802579218068600966323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 137364280422496365871820389 25755802579218068600966323)
                ·
                  refine ⟨38633703868827102901449485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25755802579218068600966323 38633703868827102901449485)
                  ·
                    refine ⟨14487638950810163588043557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 38633703868827102901449485 14487638950810163588043557)
                    ·
                      refine ⟨2716432303276905672758167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14487638950810163588043557 2716432303276905672758167)
                      ·
                        rfl

theorem cell23_5290233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 4, 1, 3, 4].length) (baseStart_5290233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5290233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5290233 prefixEnd_5290233 := by exact prefixLift 5290233
  have htrace : WordTrace (prefixWord ++ tailWord_5290233) baseStart_5290233 baseEnd_5290233 := by
    simpa [prefixWord, tailWord_5290233, baseEnd_5290233] using wordTrace_append hprefix tailTrace_5290233
  have hstable : (prefixWord ++ tailWord_5290233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5290233).length < 2 ^ (prefixWord ++ tailWord_5290233).sum := by decide
  have hdescent : baseEnd_5290233 < baseStart_5290233 := by decide
  rcases family_descends (prefixWord ++ tailWord_5290233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5290250 : List Nat := [3, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4]
def baseStart_5290250 : Nat := 118140960795 + 5290250 * 2 ^ 59
def prefixEnd_5290250 : Nat := 4983230072969 + 3 ^ 40 * 5290250 * 2
def baseEnd_5290250 : Nat := 2716441032448032106245589

theorem tailTrace_5290250 : CollatzResearch.WordTrace tailWord_5290250 prefixEnd_5290250 2716441032448032106245589 := by
  unfold tailWord_5290250
  simp only [CollatzResearch.WordTrace]
  refine ⟨48237817271083806903395051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128634179389556818409053469 48237817271083806903395051)
  ·
    refine ⟨72356725906625710355092577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48237817271083806903395051 72356725906625710355092577)
    ·
      refine ⟨54267544429969282766319433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72356725906625710355092577 54267544429969282766319433)
      ·
        refine ⟨40700658322476962074739575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54267544429969282766319433 40700658322476962074739575)
        ·
          refine ⟨61050987483715443112109363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40700658322476962074739575 61050987483715443112109363)
          ·
            refine ⟨91576481225573164668164045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61050987483715443112109363 91576481225573164668164045)
            ·
              refine ⟨34341180459589936750561517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 91576481225573164668164045 34341180459589936750561517)
              ·
                refine ⟨12877942672346226281460569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34341180459589936750561517 12877942672346226281460569)
                ·
                  refine ⟨9658457004259669711095427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12877942672346226281460569 9658457004259669711095427)
                  ·
                    refine ⟨14487685506389504566643141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9658457004259669711095427 14487685506389504566643141)
                    ·
                      refine ⟨2716441032448032106245589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14487685506389504566643141 2716441032448032106245589)
                      ·
                        rfl

theorem cell23_5290250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4].length) (baseStart_5290250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5290250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5290250 prefixEnd_5290250 := by exact prefixLift 5290250
  have htrace : WordTrace (prefixWord ++ tailWord_5290250) baseStart_5290250 baseEnd_5290250 := by
    simpa [prefixWord, tailWord_5290250, baseEnd_5290250] using wordTrace_append hprefix tailTrace_5290250
  have hstable : (prefixWord ++ tailWord_5290250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5290250).length < 2 ^ (prefixWord ++ tailWord_5290250).sum := by decide
  have hdescent : baseEnd_5290250 < baseStart_5290250 := by decide
  rcases family_descends (prefixWord ++ tailWord_5290250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5290273 : List Nat := [1, 2, 3, 2, 1, 1, 2, 3, 8]
def baseStart_5290273 : Nat := 118140960795 + 5290273 * 2 ^ 59
def prefixEnd_5290273 : Nat := 4983230072969 + 3 ^ 40 * 5290273 * 2
def baseEnd_5290273 : Nat := 301828093611453946250887

theorem tailTrace_5290273 : CollatzResearch.WordTrace tailWord_5290273 prefixEnd_5290273 301828093611453946250887 := by
  unfold tailWord_5290273
  simp only [CollatzResearch.WordTrace]
  refine ⟨192952107963251902541667473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128634738642167935027778315 192952107963251902541667473)
  ·
    refine ⟨144714080972438926906250605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192952107963251902541667473 144714080972438926906250605)
    ·
      refine ⟨54267780364664597589843977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 144714080972438926906250605 54267780364664597589843977)
      ·
        refine ⟨40700835273498448192382983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54267780364664597589843977 40700835273498448192382983)
        ·
          refine ⟨61051252910247672288574475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40700835273498448192382983 61051252910247672288574475)
          ·
            refine ⟨91576879365371508432861713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61051252910247672288574475 91576879365371508432861713)
            ·
              refine ⟨68682659524028631324646285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91576879365371508432861713 68682659524028631324646285)
              ·
                refine ⟨25755997321510736746742357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 68682659524028631324646285 25755997321510736746742357)
                ·
                  refine ⟨301828093611453946250887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25755997321510736746742357 301828093611453946250887)
                  ·
                    rfl

theorem cell23_5290273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 3, 8].length) (baseStart_5290273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5290273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5290273 prefixEnd_5290273 := by exact prefixLift 5290273
  have htrace : WordTrace (prefixWord ++ tailWord_5290273) baseStart_5290273 baseEnd_5290273 := by
    simpa [prefixWord, tailWord_5290273, baseEnd_5290273] using wordTrace_append hprefix tailTrace_5290273
  have hstable : (prefixWord ++ tailWord_5290273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5290273).length < 2 ^ (prefixWord ++ tailWord_5290273).sum := by decide
  have hdescent : baseEnd_5290273 < baseStart_5290273 := by decide
  rcases family_descends (prefixWord ++ tailWord_5290273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5290313 : List Nat := [1, 2, 1, 1, 2, 3, 1, 1, 2, 4, 5]
def baseStart_5290313 : Nat := 118140960795 + 5290313 * 2 ^ 59
def prefixEnd_5290313 : Nat := 4983230072969 + 3 ^ 40 * 5290313 * 2
def baseEnd_5290313 : Nat := 2716473381729265359757799

theorem tailTrace_5290313 : CollatzResearch.WordTrace tailWord_5290313 prefixEnd_5290313 2716473381729265359757799 := by
  unfold tailWord_5290313
  simp only [CollatzResearch.WordTrace]
  refine ⟨192953566883106989373123593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128635711255404659582082395 192953566883106989373123593)
  ·
    refine ⟨144715175162330242029842695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192953566883106989373123593 144715175162330242029842695)
    ·
      refine ⟨217072762743495363044764043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144715175162330242029842695 217072762743495363044764043)
      ·
        refine ⟨325609144115243044567146065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 217072762743495363044764043 325609144115243044567146065)
        ·
          refine ⟨244206858086432283425359549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 325609144115243044567146065 244206858086432283425359549)
          ·
            refine ⟨91577571782412106284509831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 244206858086432283425359549 91577571782412106284509831)
            ·
              refine ⟨137366357673618159426764747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91577571782412106284509831 137366357673618159426764747)
              ·
                refine ⟨206049536510427239140147121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 137366357673618159426764747 206049536510427239140147121)
                ·
                  refine ⟨154537152382820429355110341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 206049536510427239140147121 154537152382820429355110341)
                  ·
                    refine ⟨28975716071778830504083189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 154537152382820429355110341 28975716071778830504083189)
                    ·
                      refine ⟨2716473381729265359757799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28975716071778830504083189 2716473381729265359757799)
                      ·
                        rfl

theorem cell23_5290313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 1, 2, 4, 5].length) (baseStart_5290313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5290313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5290313 prefixEnd_5290313 := by exact prefixLift 5290313
  have htrace : WordTrace (prefixWord ++ tailWord_5290313) baseStart_5290313 baseEnd_5290313 := by
    simpa [prefixWord, tailWord_5290313, baseEnd_5290313] using wordTrace_append hprefix tailTrace_5290313
  have hstable : (prefixWord ++ tailWord_5290313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5290313).length < 2 ^ (prefixWord ++ tailWord_5290313).sum := by decide
  have hdescent : baseEnd_5290313 < baseStart_5290313 := by decide
  rcases family_descends (prefixWord ++ tailWord_5290313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5290327 : List Nat := [1, 1, 3, 2, 3, 1, 2, 1, 4, 3, 2]
def baseStart_5290327 : Nat := 118140960795 + 5290327 * 2 ^ 59
def prefixEnd_5290327 : Nat := 4983230072969 + 3 ^ 40 * 5290327 * 2
def baseEnd_5290327 : Nat := 2716480570458428304982735

theorem tailTrace_5290327 : CollatzResearch.WordTrace tailWord_5290327 prefixEnd_5290327 2716480570458428304982735 := by
  unfold tailWord_5290327
  simp only [CollatzResearch.WordTrace]
  refine ⟨192954077505056269764133235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128636051670037513176088823 192954077505056269764133235)
  ·
    refine ⟨289431116257584404646199853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192954077505056269764133235 289431116257584404646199853)
    ·
      refine ⟨108536668596594151742324945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 289431116257584404646199853 108536668596594151742324945)
      ·
        refine ⟨81402501447445613806743709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108536668596594151742324945 81402501447445613806743709)
        ·
          refine ⟨30525938042792105177528891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81402501447445613806743709 30525938042792105177528891)
          ·
            refine ⟨45788907064188157766293337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30525938042792105177528891 45788907064188157766293337)
            ·
              refine ⟨34341680298141118324720003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45788907064188157766293337 34341680298141118324720003)
              ·
                refine ⟨51512520447211677487080005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34341680298141118324720003 51512520447211677487080005)
                ·
                  refine ⟨9658597583852189528827501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 51512520447211677487080005 9658597583852189528827501)
                  ·
                    refine ⟨3621974093944571073310313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9658597583852189528827501 3621974093944571073310313)
                    ·
                      refine ⟨2716480570458428304982735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3621974093944571073310313 2716480570458428304982735)
                      ·
                        rfl

theorem cell23_5290327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 1, 4, 3, 2].length) (baseStart_5290327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5290327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5290327 prefixEnd_5290327 := by exact prefixLift 5290327
  have htrace : WordTrace (prefixWord ++ tailWord_5290327) baseStart_5290327 baseEnd_5290327 := by
    simpa [prefixWord, tailWord_5290327, baseEnd_5290327] using wordTrace_append hprefix tailTrace_5290327
  have hstable : (prefixWord ++ tailWord_5290327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5290327).length < 2 ^ (prefixWord ++ tailWord_5290327).sum := by decide
  have hdescent : baseEnd_5290327 < baseStart_5290327 := by decide
  rcases family_descends (prefixWord ++ tailWord_5290327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5290377 : List Nat := [1, 2, 1, 1, 6, 2, 2, 1, 1, 1, 5]
def baseStart_5290377 : Nat := 118140960795 + 5290377 * 2 ^ 59
def prefixEnd_5290377 : Nat := 4983230072969 + 3 ^ 40 * 5290377 * 2
def baseEnd_5290377 : Nat := 2716506244491153109357505

theorem tailTrace_5290377 : CollatzResearch.WordTrace tailWord_5290377 prefixEnd_5290377 2716506244491153109357505 := by
  unfold tailWord_5290377
  simp only [CollatzResearch.WordTrace]
  refine ⟨192955901154875128303453385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128637267436583418868968923 192955901154875128303453385)
  ·
    refine ⟨144716925866156346227590039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192955901154875128303453385 144716925866156346227590039)
    ·
      refine ⟨217075388799234519341385059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144716925866156346227590039 217075388799234519341385059)
      ·
        refine ⟨325613083198851779012077589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 217075388799234519341385059 325613083198851779012077589)
        ·
          refine ⟨15263113274946177141191137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 325613083198851779012077589 15263113274946177141191137)
          ·
            refine ⟨11447334956209632855893353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15263113274946177141191137 11447334956209632855893353)
            ·
              refine ⟨8585501217157224641920015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11447334956209632855893353 8585501217157224641920015)
              ·
                refine ⟨12878251825735836962880023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8585501217157224641920015 12878251825735836962880023)
                ·
                  refine ⟨19317377738603755444320035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12878251825735836962880023 19317377738603755444320035)
                  ·
                    refine ⟨28976066607905633166480053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19317377738603755444320035 28976066607905633166480053)
                    ·
                      refine ⟨2716506244491153109357505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28976066607905633166480053 2716506244491153109357505)
                      ·
                        rfl

theorem cell23_5290377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 2, 1, 1, 1, 5].length) (baseStart_5290377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5290377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5290377 prefixEnd_5290377 := by exact prefixLift 5290377
  have htrace : WordTrace (prefixWord ++ tailWord_5290377) baseStart_5290377 baseEnd_5290377 := by
    simpa [prefixWord, tailWord_5290377, baseEnd_5290377] using wordTrace_append hprefix tailTrace_5290377
  have hstable : (prefixWord ++ tailWord_5290377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5290377).length < 2 ^ (prefixWord ++ tailWord_5290377).sum := by decide
  have hdescent : baseEnd_5290377 < baseStart_5290377 := by decide
  rcases family_descends (prefixWord ++ tailWord_5290377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5290380 : List Nat := [2, 2, 1, 2, 1, 6, 9]
def baseStart_5290380 : Nat := 118140960795 + 5290380 * 2 ^ 59
def prefixEnd_5290380 : Nat := 4983230072969 + 3 ^ 40 * 5290380 * 2
def baseEnd_5290380 : Nat := 33537133147322427131111

theorem tailTrace_5290380 : CollatzResearch.WordTrace tailWord_5290380 prefixEnd_5290380 33537133147322427131111 := by
  unfold tailWord_5290380
  simp only [CollatzResearch.WordTrace]
  refine ⟨96478005286932129907906297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128637340382576173210541729 96478005286932129907906297)
  ·
    refine ⟨72358503965199097430929723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96478005286932129907906297 72358503965199097430929723)
    ·
      refine ⟨108537755947798646146394585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72358503965199097430929723 108537755947798646146394585)
      ·
        refine ⟨81403316960848984609795939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108537755947798646146394585 81403316960848984609795939)
        ·
          refine ⟨122104975441273476914693909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81403316960848984609795939 122104975441273476914693909)
          ·
            refine ⟨5723670723809694230376277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 122104975441273476914693909 5723670723809694230376277)
            ·
              refine ⟨33537133147322427131111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5723670723809694230376277 33537133147322427131111)
              ·
                rfl

theorem cell23_5290380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 9].length) (baseStart_5290380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5290380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5290380 prefixEnd_5290380 := by exact prefixLift 5290380
  have htrace : WordTrace (prefixWord ++ tailWord_5290380) baseStart_5290380 baseEnd_5290380 := by
    simpa [prefixWord, tailWord_5290380, baseEnd_5290380] using wordTrace_append hprefix tailTrace_5290380
  have hstable : (prefixWord ++ tailWord_5290380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5290380).length < 2 ^ (prefixWord ++ tailWord_5290380).sum := by decide
  have hdescent : baseEnd_5290380 < baseStart_5290380 := by decide
  rcases family_descends (prefixWord ++ tailWord_5290380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5290391 : List Nat := [1, 1, 3, 3, 1, 1, 2, 6, 1, 2, 2]
def baseStart_5290391 : Nat := 118140960795 + 5290391 * 2 ^ 59
def prefixEnd_5290391 : Nat := 4983230072969 + 3 ^ 40 * 5290391 * 2
def baseEnd_5290391 : Nat := 2716513433220316054582441

theorem tailTrace_5290391 : CollatzResearch.WordTrace tailWord_5290391 prefixEnd_5290391 2716513433220316054582441 := by
  unfold tailWord_5290391
  simp only [CollatzResearch.WordTrace]
  refine ⟨192956411776824408694463027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128637607851216272462975351 192956411776824408694463027)
  ·
    refine ⟨289434617665236613041694541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192956411776824408694463027 289434617665236613041694541)
    ·
      refine ⟨108537981624463729890635453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 289434617665236613041694541 108537981624463729890635453)
      ·
        refine ⟨40701743109173898708988295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 108537981624463729890635453 40701743109173898708988295)
        ·
          refine ⟨61052614663760848063482443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40701743109173898708988295 61052614663760848063482443)
          ·
            refine ⟨91578921995641272095223665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61052614663760848063482443 91578921995641272095223665)
            ·
              refine ⟨68684191496730954071417749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91578921995641272095223665 68684191496730954071417749)
              ·
                refine ⟨3219571476409263472097707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 68684191496730954071417749 3219571476409263472097707)
                ·
                  refine ⟨4829357214613895208146561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3219571476409263472097707 4829357214613895208146561)
                  ·
                    refine ⟨3622017910960421406109921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4829357214613895208146561 3622017910960421406109921)
                    ·
                      refine ⟨2716513433220316054582441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3622017910960421406109921 2716513433220316054582441)
                      ·
                        rfl

theorem cell23_5290391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 6, 1, 2, 2].length) (baseStart_5290391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5290391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5290391 prefixEnd_5290391 := by exact prefixLift 5290391
  have htrace : WordTrace (prefixWord ++ tailWord_5290391) baseStart_5290391 baseEnd_5290391 := by
    simpa [prefixWord, tailWord_5290391, baseEnd_5290391] using wordTrace_append hprefix tailTrace_5290391
  have hstable : (prefixWord ++ tailWord_5290391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5290391).length < 2 ^ (prefixWord ++ tailWord_5290391).sum := by decide
  have hdescent : baseEnd_5290391 < baseStart_5290391 := by decide
  rcases family_descends (prefixWord ++ tailWord_5290391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5290397 : List Nat := [1, 4, 2, 1, 4, 1, 2, 8]
def baseStart_5290397 : Nat := 118140960795 + 5290397 * 2 ^ 59
def prefixEnd_5290397 : Nat := 4983230072969 + 3 ^ 40 * 5290397 * 2
def baseEnd_5290397 : Nat := 100611722744601593744719

theorem tailTrace_5290397 : CollatzResearch.WordTrace tailWord_5290397 prefixEnd_5290397 100611722744601593744719 := by
  unfold tailWord_5290397
  simp only [CollatzResearch.WordTrace]
  refine ⟨192956630614802671719181445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128637753743201781146120963 192956630614802671719181445)
  ·
    refine ⟨36179368240275500947346521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 192956630614802671719181445 36179368240275500947346521)
    ·
      refine ⟨27134526180206625710509891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36179368240275500947346521 27134526180206625710509891)
      ·
        refine ⟨40701789270309938565764837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27134526180206625710509891 40701789270309938565764837)
        ·
          refine ⟨7631585488183113481080907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40701789270309938565764837 7631585488183113481080907)
          ·
            refine ⟨11447378232274670221621361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7631585488183113481080907 11447378232274670221621361)
            ·
              refine ⟨8585533674206002666216021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11447378232274670221621361 8585533674206002666216021)
              ·
                refine ⟨100611722744601593744719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8585533674206002666216021 100611722744601593744719)
                ·
                  rfl

theorem cell23_5290397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 2, 8].length) (baseStart_5290397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5290397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5290397 prefixEnd_5290397 := by exact prefixLift 5290397
  have htrace : WordTrace (prefixWord ++ tailWord_5290397) baseStart_5290397 baseEnd_5290397 := by
    simpa [prefixWord, tailWord_5290397, baseEnd_5290397] using wordTrace_append hprefix tailTrace_5290397
  have hstable : (prefixWord ++ tailWord_5290397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5290397).length < 2 ^ (prefixWord ++ tailWord_5290397).sum := by decide
  have hdescent : baseEnd_5290397 < baseStart_5290397 := by decide
  rcases family_descends (prefixWord ++ tailWord_5290397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5290401 : List Nat := [1, 2, 3, 5, 1, 1, 1, 3, 2, 4]
def baseStart_5290401 : Nat := 118140960795 + 5290401 * 2 ^ 59
def prefixEnd_5290401 : Nat := 4983230072969 + 3 ^ 40 * 5290401 * 2
def baseEnd_5290401 : Nat := 905506189342287005152465

theorem tailTrace_5290401 : CollatzResearch.WordTrace tailWord_5290401 prefixEnd_5290401 905506189342287005152465 := by
  unfold tailWord_5290401
  simp only [CollatzResearch.WordTrace]
  refine ⟨192956776506788180402327057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128637851004525453601551371 192956776506788180402327057)
  ·
    refine ⟨144717582380091135301745293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192956776506788180402327057 144717582380091135301745293)
    ·
      refine ⟨54269093392534175738154485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 144717582380091135301745293 54269093392534175738154485)
      ·
        refine ⟨5087727505550078975451983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 54269093392534175738154485 5087727505550078975451983)
        ·
          refine ⟨7631591258325118463177975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5087727505550078975451983 7631591258325118463177975)
          ·
            refine ⟨11447386887487677694766963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7631591258325118463177975 11447386887487677694766963)
            ·
              refine ⟨17171080331231516542150445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11447386887487677694766963 17171080331231516542150445)
              ·
                refine ⟨6439155124211818703306417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17171080331231516542150445 6439155124211818703306417)
                ·
                  refine ⟨4829366343158864027479813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6439155124211818703306417 4829366343158864027479813)
                  ·
                    refine ⟨905506189342287005152465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4829366343158864027479813 905506189342287005152465)
                    ·
                      rfl

theorem cell23_5290401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 1, 3, 2, 4].length) (baseStart_5290401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5290401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5290401 prefixEnd_5290401 := by exact prefixLift 5290401
  have htrace : WordTrace (prefixWord ++ tailWord_5290401) baseStart_5290401 baseEnd_5290401 := by
    simpa [prefixWord, tailWord_5290401, baseEnd_5290401] using wordTrace_append hprefix tailTrace_5290401
  have hstable : (prefixWord ++ tailWord_5290401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5290401).length < 2 ^ (prefixWord ++ tailWord_5290401).sum := by decide
  have hdescent : baseEnd_5290401 < baseStart_5290401 := by decide
  rcases family_descends (prefixWord ++ tailWord_5290401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5290447 : List Nat := [1, 1, 2, 1, 1, 4, 1, 1, 5, 4, 2]
def baseStart_5290447 : Nat := 118140960795 + 5290447 * 2 ^ 59
def prefixEnd_5290447 : Nat := 4983230072969 + 3 ^ 40 * 5290447 * 2
def baseEnd_5290447 : Nat := 2716542188136967835482183

theorem tailTrace_5290447 : CollatzResearch.WordTrace tailWord_5290447 prefixEnd_5290447 2716542188136967835482183 := by
  unfold tailWord_5290447
  simp only [CollatzResearch.WordTrace]
  refine ⟨192958454264621530258501595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128638969509747686839001063 192958454264621530258501595)
  ·
    refine ⟨289437681396932295387752393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192958454264621530258501595 289437681396932295387752393)
    ·
      refine ⟨217078261047699221540814295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 289437681396932295387752393 217078261047699221540814295)
      ·
        refine ⟨325617391571548832311221443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 217078261047699221540814295 325617391571548832311221443)
        ·
          refine ⟨488426087357323248466832165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 325617391571548832311221443 488426087357323248466832165)
          ·
            refine ⟨91579891379498109087531031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 488426087357323248466832165 91579891379498109087531031)
            ·
              refine ⟨137369837069247163631296547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91579891379498109087531031 137369837069247163631296547)
              ·
                refine ⟨206054755603870745446944821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 137369837069247163631296547 206054755603870745446944821)
                ·
                  refine ⟨19317633337862882385651077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 206054755603870745446944821 19317633337862882385651077)
                  ·
                    refine ⟨3622056250849290447309577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19317633337862882385651077 3622056250849290447309577)
                    ·
                      refine ⟨2716542188136967835482183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3622056250849290447309577 2716542188136967835482183)
                      ·
                        rfl

theorem cell23_5290447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 1, 5, 4, 2].length) (baseStart_5290447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5290447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5290447 prefixEnd_5290447 := by exact prefixLift 5290447
  have htrace : WordTrace (prefixWord ++ tailWord_5290447) baseStart_5290447 baseEnd_5290447 := by
    simpa [prefixWord, tailWord_5290447, baseEnd_5290447] using wordTrace_append hprefix tailTrace_5290447
  have hstable : (prefixWord ++ tailWord_5290447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5290447).length < 2 ^ (prefixWord ++ tailWord_5290447).sum := by decide
  have hdescent : baseEnd_5290447 < baseStart_5290447 := by decide
  rcases family_descends (prefixWord ++ tailWord_5290447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5290464 : List Nat := [2, 1, 1, 3, 1, 1, 6, 1, 1, 4, 2]
def baseStart_5290464 : Nat := 118140960795 + 5290464 * 2 ^ 59
def prefixEnd_5290464 : Nat := 4983230072969 + 3 ^ 40 * 5290464 * 2
def baseEnd_5290464 : Nat := 2716550917308094268969605

theorem tailTrace_5290464 : CollatzResearch.WordTrace tailWord_5290464 prefixEnd_5290464 2716550917308094268969605 := by
  unfold tailWord_5290464
  simp only [CollatzResearch.WordTrace]
  refine ⟨96479537152779971080935223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128639382870373294774580297 96479537152779971080935223)
  ·
    refine ⟨144719305729169956621402835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96479537152779971080935223 144719305729169956621402835)
    ·
      refine ⟨217078958593754934932104253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144719305729169956621402835 217078958593754934932104253)
      ·
        refine ⟨81404609472658100599539095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 217078958593754934932104253 81404609472658100599539095)
        ·
          refine ⟨122106914208987150899308643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81404609472658100599539095 122106914208987150899308643)
          ·
            refine ⟨183160371313480726348962965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122106914208987150899308643 183160371313480726348962965)
            ·
              refine ⟨8585642405319409047607639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 183160371313480726348962965 8585642405319409047607639)
              ·
                refine ⟨12878463607979113571411459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8585642405319409047607639 12878463607979113571411459)
                ·
                  refine ⟨19317695411968670357117189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12878463607979113571411459 19317695411968670357117189)
                  ·
                    refine ⟨3622067889744125691959473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19317695411968670357117189 3622067889744125691959473)
                    ·
                      refine ⟨2716550917308094268969605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3622067889744125691959473 2716550917308094268969605)
                      ·
                        rfl

theorem cell23_5290464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 6, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 6, 1, 1, 4, 2].length) (baseStart_5290464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5290464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5290464 prefixEnd_5290464 := by exact prefixLift 5290464
  have htrace : WordTrace (prefixWord ++ tailWord_5290464) baseStart_5290464 baseEnd_5290464 := by
    simpa [prefixWord, tailWord_5290464, baseEnd_5290464] using wordTrace_append hprefix tailTrace_5290464
  have hstable : (prefixWord ++ tailWord_5290464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5290464).length < 2 ^ (prefixWord ++ tailWord_5290464).sum := by decide
  have hdescent : baseEnd_5290464 < baseStart_5290464 := by decide
  rcases family_descends (prefixWord ++ tailWord_5290464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5290554 : List Nat := [3, 1, 1, 1, 3, 4, 1, 2, 2, 1, 4]
def baseStart_5290554 : Nat := 118140960795 + 5290554 * 2 ^ 59
def prefixEnd_5290554 : Nat := 4983230072969 + 3 ^ 40 * 5290554 * 2
def baseEnd_5290554 : Nat := 2716597130566998916844191

theorem tailTrace_5290554 : CollatzResearch.WordTrace tailWord_5290554 prefixEnd_5290554 2716597130566998916844191 := by
  unfold tailWord_5290554
  simp only [CollatzResearch.WordTrace]
  refine ⟨48240589218808471883161679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128641571250155925021764477 48240589218808471883161679)
  ·
    refine ⟨72360883828212707824742519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48240589218808471883161679 72360883828212707824742519)
    ·
      refine ⟨108541325742319061737113779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72360883828212707824742519 108541325742319061737113779)
      ·
        refine ⟨162811988613478592605670669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108541325742319061737113779 162811988613478592605670669)
        ·
          refine ⟨61054495730054472227126501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 162811988613478592605670669 61054495730054472227126501)
          ·
            refine ⟨11447717949385213542586219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 61054495730054472227126501 11447717949385213542586219)
            ·
              refine ⟨17171576924077820313879329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11447717949385213542586219 17171576924077820313879329)
              ·
                refine ⟨12878682693058365235409497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17171576924077820313879329 12878682693058365235409497)
                ·
                  refine ⟨9659012019793773926557123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12878682693058365235409497 9659012019793773926557123)
                  ·
                    refine ⟨14488518029690660889835685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9659012019793773926557123 14488518029690660889835685)
                    ·
                      refine ⟨2716597130566998916844191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14488518029690660889835685 2716597130566998916844191)
                      ·
                        rfl

theorem cell23_5290554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 1, 2, 2, 1, 4].length) (baseStart_5290554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5290554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5290554 prefixEnd_5290554 := by exact prefixLift 5290554
  have htrace : WordTrace (prefixWord ++ tailWord_5290554) baseStart_5290554 baseEnd_5290554 := by
    simpa [prefixWord, tailWord_5290554, baseEnd_5290554] using wordTrace_append hprefix tailTrace_5290554
  have hstable : (prefixWord ++ tailWord_5290554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5290554).length < 2 ^ (prefixWord ++ tailWord_5290554).sum := by decide
  have hdescent : baseEnd_5290554 < baseStart_5290554 := by decide
  rcases family_descends (prefixWord ++ tailWord_5290554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5290661 : List Nat := [1, 3, 1, 2, 1, 2, 1, 1, 7, 2, 2]
def baseStart_5290661 : Nat := 118140960795 + 5290661 * 2 ^ 59
def prefixEnd_5290661 : Nat := 4983230072969 + 3 ^ 40 * 5290661 * 2
def baseEnd_5290661 : Nat := 2716652072997029998206199

theorem tailTrace_5290661 : CollatzResearch.WordTrace tailWord_5290661 prefixEnd_5290661 2716652072997029998206199 := by
  unfold tailWord_5290661
  simp only [CollatzResearch.WordTrace]
  refine ⟨192966259485846244806791837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128644172990564163204527891 192966259485846244806791837)
  ·
    refine ⟨72362347307192341802546939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 192966259485846244806791837 72362347307192341802546939)
    ·
      refine ⟨108543520960788512703820409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72362347307192341802546939 108543520960788512703820409)
      ·
        refine ⟨81407640720591384527865307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108543520960788512703820409 81407640720591384527865307)
        ·
          refine ⟨122111461080887076791797961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81407640720591384527865307 122111461080887076791797961)
          ·
            refine ⟨91583595810665307593848471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 122111461080887076791797961 91583595810665307593848471)
            ·
              refine ⟨137375393715997961390772707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91583595810665307593848471 137375393715997961390772707)
              ·
                refine ⟨206063090573996942086159061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 137375393715997961390772707 206063090573996942086159061)
                ·
                  refine ⟨4829603685328053330144353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 206063090573996942086159061 4829603685328053330144353)
                  ·
                    refine ⟨3622202763996039997608265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4829603685328053330144353 3622202763996039997608265)
                    ·
                      refine ⟨2716652072997029998206199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3622202763996039997608265 2716652072997029998206199)
                      ·
                        rfl

theorem cell23_5290661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 1, 7, 2, 2].length) (baseStart_5290661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5290661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5290661 prefixEnd_5290661 := by exact prefixLift 5290661
  have htrace : WordTrace (prefixWord ++ tailWord_5290661) baseStart_5290661 baseEnd_5290661 := by
    simpa [prefixWord, tailWord_5290661, baseEnd_5290661] using wordTrace_append hprefix tailTrace_5290661
  have hstable : (prefixWord ++ tailWord_5290661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5290661).length < 2 ^ (prefixWord ++ tailWord_5290661).sum := by decide
  have hdescent : baseEnd_5290661 < baseStart_5290661 := by decide
  rcases family_descends (prefixWord ++ tailWord_5290661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5290671 : List Nat := [1, 1, 2, 1, 2, 5, 3, 2, 2, 4]
def baseStart_5290671 : Nat := 118140960795 + 5290671 * 2 ^ 59
def prefixEnd_5290671 : Nat := 4983230072969 + 3 ^ 40 * 5290671 * 2
def baseEnd_5290671 : Nat := 905552402601191653027051

theorem tailTrace_5290671 : CollatzResearch.WordTrace tailWord_5290671 prefixEnd_5290671 905552402601191653027051 := by
  unfold tailWord_5290671
  simp only [CollatzResearch.WordTrace]
  refine ⟨192966624215810016514655867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128644416143873344343103911 192966624215810016514655867)
  ·
    refine ⟨289449936323715024771983801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192966624215810016514655867 289449936323715024771983801)
    ·
      refine ⟨217087452242786268578987851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 289449936323715024771983801 217087452242786268578987851)
      ·
        refine ⟨325631178364179402868481777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 217087452242786268578987851 325631178364179402868481777)
        ·
          refine ⟨244223383773134552151361333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 325631178364179402868481777 244223383773134552151361333)
          ·
            refine ⟨22895942228731364264190125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 244223383773134552151361333 22895942228731364264190125)
            ·
              refine ⟨8585978335774261599071297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22895942228731364264190125 8585978335774261599071297)
              ·
                refine ⟨6439483751830696199303473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8585978335774261599071297 6439483751830696199303473)
                ·
                  refine ⟨4829612813873022149477605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6439483751830696199303473 4829612813873022149477605)
                  ·
                    refine ⟨905552402601191653027051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4829612813873022149477605 905552402601191653027051)
                    ·
                      rfl

theorem cell23_5290671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 3, 2, 2, 4].length) (baseStart_5290671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5290671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5290671 prefixEnd_5290671 := by exact prefixLift 5290671
  have htrace : WordTrace (prefixWord ++ tailWord_5290671) baseStart_5290671 baseEnd_5290671 := by
    simpa [prefixWord, tailWord_5290671, baseEnd_5290671] using wordTrace_append hprefix tailTrace_5290671
  have hstable : (prefixWord ++ tailWord_5290671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5290671).length < 2 ^ (prefixWord ++ tailWord_5290671).sum := by decide
  have hdescent : baseEnd_5290671 < baseStart_5290671 := by decide
  rcases family_descends (prefixWord ++ tailWord_5290671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5290688 : List Nat := [2, 1, 1, 2, 4, 3, 3, 1, 2, 4]
def baseStart_5290688 : Nat := 118140960795 + 5290688 * 2 ^ 59
def prefixEnd_5290688 : Nat := 4983230072969 + 3 ^ 40 * 5290688 * 2
def baseEnd_5290688 : Nat := 905555312324900464189525

theorem tailTrace_5290688 : CollatzResearch.WordTrace tailWord_5290688 prefixEnd_5290688 905555312324900464189525 := by
  unfold tailWord_5290688
  simp only [CollatzResearch.WordTrace]
  refine ⟨96483622128374214209012359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128644829504498952278683145 96483622128374214209012359)
  ·
    refine ⟨144725433192561321313518539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96483622128374214209012359 144725433192561321313518539)
    ·
      refine ⟨217088149788841981970277809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144725433192561321313518539 217088149788841981970277809)
      ·
        refine ⟨162816112341631486477708357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 217088149788841981970277809 162816112341631486477708357)
        ·
          refine ⟨30528021064055903714570317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 162816112341631486477708357 30528021064055903714570317)
          ·
            refine ⟨11448007899020963892963869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30528021064055903714570317 11448007899020963892963869)
            ·
              refine ⟨4293002962132861459861451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11448007899020963892963869 4293002962132861459861451)
              ·
                refine ⟨6439504443199292189792177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4293002962132861459861451 6439504443199292189792177)
                ·
                  refine ⟨4829628332399469142344133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6439504443199292189792177 4829628332399469142344133)
                  ·
                    refine ⟨905555312324900464189525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4829628332399469142344133 905555312324900464189525)
                    ·
                      rfl

theorem cell23_5290688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 3, 1, 2, 4].length) (baseStart_5290688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5290688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5290688 prefixEnd_5290688 := by exact prefixLift 5290688
  have htrace : WordTrace (prefixWord ++ tailWord_5290688) baseStart_5290688 baseEnd_5290688 := by
    simpa [prefixWord, tailWord_5290688, baseEnd_5290688] using wordTrace_append hprefix tailTrace_5290688
  have hstable : (prefixWord ++ tailWord_5290688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5290688).length < 2 ^ (prefixWord ++ tailWord_5290688).sum := by decide
  have hdescent : baseEnd_5290688 < baseStart_5290688 := by decide
  rcases family_descends (prefixWord ++ tailWord_5290688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5290698 : List Nat := [3, 1, 2, 1, 4, 2, 2, 2, 1, 2, 3]
def baseStart_5290698 : Nat := 118140960795 + 5290698 * 2 ^ 59
def prefixEnd_5290698 : Nat := 4983230072969 + 3 ^ 40 * 5290698 * 2
def baseEnd_5290698 : Nat := 2716671071781246353443529

theorem tailTrace_5290698 : CollatzResearch.WordTrace tailWord_5290698 prefixEnd_5290698 2716671071781246353443529 := by
  unfold tailWord_5290698
  simp only [CollatzResearch.WordTrace]
  refine ⟨48241902246678050031472187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128645072657808133417259165 48241902246678050031472187)
  ·
    refine ⟨72362853370017075047208281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48241902246678050031472187 72362853370017075047208281)
    ·
      refine ⟨54272140027512806285406211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72362853370017075047208281 54272140027512806285406211)
      ·
        refine ⟨81408210041269209428109317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54272140027512806285406211 81408210041269209428109317)
        ·
          refine ⟨15264039382737976767770497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 81408210041269209428109317 15264039382737976767770497)
          ·
            refine ⟨11448029537053482575827873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15264039382737976767770497 11448029537053482575827873)
            ·
              refine ⟨8586022152790111931870905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11448029537053482575827873 8586022152790111931870905)
              ·
                refine ⟨6439516614592583948903179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8586022152790111931870905 6439516614592583948903179)
                ·
                  refine ⟨9659274921888875923354769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6439516614592583948903179 9659274921888875923354769)
                  ·
                    refine ⟨7244456191416656942516077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9659274921888875923354769 7244456191416656942516077)
                    ·
                      refine ⟨2716671071781246353443529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7244456191416656942516077 2716671071781246353443529)
                      ·
                        rfl

theorem cell23_5290698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 2, 2, 1, 2, 3].length) (baseStart_5290698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5290698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5290698 prefixEnd_5290698 := by exact prefixLift 5290698
  have htrace : WordTrace (prefixWord ++ tailWord_5290698) baseStart_5290698 baseEnd_5290698 := by
    simpa [prefixWord, tailWord_5290698, baseEnd_5290698] using wordTrace_append hprefix tailTrace_5290698
  have hstable : (prefixWord ++ tailWord_5290698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5290698).length < 2 ^ (prefixWord ++ tailWord_5290698).sum := by decide
  have hdescent : baseEnd_5290698 < baseStart_5290698 := by decide
  rcases family_descends (prefixWord ++ tailWord_5290698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5290711 : List Nat := [1, 1, 3, 2, 1, 4, 1, 2, 4, 1, 3]
def baseStart_5290711 : Nat := 118140960795 + 5290711 * 2 ^ 59
def prefixEnd_5290711 : Nat := 4983230072969 + 3 ^ 40 * 5290711 * 2
def baseEnd_5290711 : Nat := 2716677747029754802580969

theorem tailTrace_5290711 : CollatzResearch.WordTrace tailWord_5290711 prefixEnd_5290711 2716677747029754802580969 := by
  unfold tailWord_5290711
  simp only [CollatzResearch.WordTrace]
  refine ⟨192968083135665103346111987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128645388757110068897407991 192968083135665103346111987)
  ·
    refine ⟨289452124703497655019167981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192968083135665103346111987 289452124703497655019167981)
    ·
      refine ⟨108544546763811620632187993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 289452124703497655019167981 108544546763811620632187993)
      ·
        refine ⟨81408410072858715474140995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108544546763811620632187993 81408410072858715474140995)
        ·
          refine ⟨122112615109288073211211493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81408410072858715474140995 122112615109288073211211493)
          ·
            refine ⟨22896115332991513727102155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 122112615109288073211211493 22896115332991513727102155)
            ·
              refine ⟨34344172999487270590653233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22896115332991513727102155 34344172999487270590653233)
              ·
                refine ⟨25758129749615452942989925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34344172999487270590653233 25758129749615452942989925)
                ·
                  refine ⟨4829649328052897426810611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25758129749615452942989925 4829649328052897426810611)
                  ·
                    refine ⟨7244473992079346140215917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4829649328052897426810611 7244473992079346140215917)
                    ·
                      refine ⟨2716677747029754802580969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7244473992079346140215917 2716677747029754802580969)
                      ·
                        rfl

theorem cell23_5290711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 2, 4, 1, 3].length) (baseStart_5290711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5290711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5290711 prefixEnd_5290711 := by exact prefixLift 5290711
  have htrace : WordTrace (prefixWord ++ tailWord_5290711) baseStart_5290711 baseEnd_5290711 := by
    simpa [prefixWord, tailWord_5290711, baseEnd_5290711] using wordTrace_append hprefix tailTrace_5290711
  have hstable : (prefixWord ++ tailWord_5290711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5290711).length < 2 ^ (prefixWord ++ tailWord_5290711).sum := by decide
  have hdescent : baseEnd_5290711 < baseStart_5290711 := by decide
  rcases family_descends (prefixWord ++ tailWord_5290711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5290712 : List Nat := [2, 1, 2, 2, 3, 4, 1, 3, 1, 2, 2]
def baseStart_5290712 : Nat := 118140960795 + 5290712 * 2 ^ 59
def prefixEnd_5290712 : Nat := 4983230072969 + 3 ^ 40 * 5290712 * 2
def baseEnd_5290712 : Nat := 2716678260510409298668465

theorem tailTrace_5290712 : CollatzResearch.WordTrace tailWord_5290712 prefixEnd_5290712 2716678260510409298668465 := by
  unfold tailWord_5290712
  simp only [CollatzResearch.WordTrace]
  refine ⟨96484059804330740258449195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128645413072440987011265593 96484059804330740258449195)
  ·
    refine ⟨144726089706496110387673793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96484059804330740258449195 144726089706496110387673793)
    ·
      refine ⟨108544567279872082790755345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144726089706496110387673793 108544567279872082790755345)
      ·
        refine ⟨81408425459904062093066509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108544567279872082790755345 81408425459904062093066509)
        ·
          refine ⟨30528159547464023284899941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81408425459904062093066509 30528159547464023284899941)
          ·
            refine ⟨5724029915149504365918739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30528159547464023284899941 5724029915149504365918739)
            ·
              refine ⟨8586044872724256548878109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5724029915149504365918739 8586044872724256548878109)
              ·
                refine ⟨3219766827271596205829291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8586044872724256548878109 3219766827271596205829291)
                ·
                  refine ⟨4829650240907394308743937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3219766827271596205829291 4829650240907394308743937)
                  ·
                    refine ⟨3622237680680545731557953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4829650240907394308743937 3622237680680545731557953)
                    ·
                      refine ⟨2716678260510409298668465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3622237680680545731557953 2716678260510409298668465)
                      ·
                        rfl

theorem cell23_5290712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 1, 3, 1, 2, 2].length) (baseStart_5290712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5290712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5290712 prefixEnd_5290712 := by exact prefixLift 5290712
  have htrace : WordTrace (prefixWord ++ tailWord_5290712) baseStart_5290712 baseEnd_5290712 := by
    simpa [prefixWord, tailWord_5290712, baseEnd_5290712] using wordTrace_append hprefix tailTrace_5290712
  have hstable : (prefixWord ++ tailWord_5290712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5290712).length < 2 ^ (prefixWord ++ tailWord_5290712).sum := by decide
  have hdescent : baseEnd_5290712 < baseStart_5290712 := by decide
  rcases family_descends (prefixWord ++ tailWord_5290712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5290751 : List Nat := [1, 1, 2, 2, 1, 3, 1, 5, 1, 4, 2]
def baseStart_5290751 : Nat := 118140960795 + 5290751 * 2 ^ 59
def prefixEnd_5290751 : Nat := 4983230072969 + 3 ^ 40 * 5290751 * 2
def baseEnd_5290751 : Nat := 2716698286255934646080785

theorem tailTrace_5290751 : CollatzResearch.WordTrace tailWord_5290751 prefixEnd_5290751 2716698286255934646080785 := by
  unfold tailWord_5290751
  simp only [CollatzResearch.WordTrace]
  refine ⟨192969542055520190177568107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128646361370346793451712071 192969542055520190177568107)
  ·
    refine ⟨289454313083280285266352161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192969542055520190177568107 289454313083280285266352161)
    ·
      refine ⟨217090734812460213949764121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 289454313083280285266352161 217090734812460213949764121)
      ·
        refine ⟨162818051109345160462323091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 217090734812460213949764121 162818051109345160462323091)
        ·
          refine ⟨244227076664017740693484637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162818051109345160462323091 244227076664017740693484637)
          ·
            refine ⟨91585153749006652760056739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 244227076664017740693484637 91585153749006652760056739)
            ·
              refine ⟨137377730623509979140085109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91585153749006652760056739 137377730623509979140085109)
              ·
                refine ⟨12879162245954060544382979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 137377730623509979140085109 12879162245954060544382979)
                ·
                  refine ⟨19318743368931090816574469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12879162245954060544382979 19318743368931090816574469)
                  ·
                    refine ⟨3622264381674579528107713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19318743368931090816574469 3622264381674579528107713)
                    ·
                      refine ⟨2716698286255934646080785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3622264381674579528107713 2716698286255934646080785)
                      ·
                        rfl

theorem cell23_5290751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 5, 1, 4, 2].length) (baseStart_5290751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5290751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5290751 prefixEnd_5290751 := by exact prefixLift 5290751
  have htrace : WordTrace (prefixWord ++ tailWord_5290751) baseStart_5290751 baseEnd_5290751 := by
    simpa [prefixWord, tailWord_5290751, baseEnd_5290751] using wordTrace_append hprefix tailTrace_5290751
  have hstable : (prefixWord ++ tailWord_5290751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5290751).length < 2 ^ (prefixWord ++ tailWord_5290751).sum := by decide
  have hdescent : baseEnd_5290751 < baseStart_5290751 := by decide
  rcases family_descends (prefixWord ++ tailWord_5290751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5290764 : List Nat := [2, 2, 1, 2, 2, 1, 1, 2, 4, 2, 4]
def baseStart_5290764 : Nat := 118140960795 + 5290764 * 2 ^ 59
def prefixEnd_5290764 : Nat := 4983230072969 + 3 ^ 40 * 5290764 * 2
def baseEnd_5290764 : Nat := 2716704961504443095218225

theorem tailTrace_5290764 : CollatzResearch.WordTrace tailWord_5290764 prefixEnd_5290764 2716704961504443095218225 := by
  unfold tailWord_5290764
  simp only [CollatzResearch.WordTrace]
  refine ⟨96485008102236546698895673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128646677469648728931860897 96485008102236546698895673)
  ·
    refine ⟨72363756076677410024171755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96485008102236546698895673 72363756076677410024171755)
    ·
      refine ⟨108545634115016115036257633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72363756076677410024171755 108545634115016115036257633)
      ·
        refine ⟨81409225586262086277193225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108545634115016115036257633 81409225586262086277193225)
        ·
          refine ⟨61056919189696564707894919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81409225586262086277193225 61056919189696564707894919)
          ·
            refine ⟨91585378784544847061842379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61056919189696564707894919 91585378784544847061842379)
            ·
              refine ⟨137378068176817270592763569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91585378784544847061842379 137378068176817270592763569)
              ·
                refine ⟨103033551132612952944572677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 137378068176817270592763569 103033551132612952944572677)
                ·
                  refine ⟨19318790837364928677107377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 103033551132612952944572677 19318790837364928677107377)
                  ·
                    refine ⟨14489093128023696507830533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19318790837364928677107377 14489093128023696507830533)
                    ·
                      refine ⟨2716704961504443095218225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14489093128023696507830533 2716704961504443095218225)
                      ·
                        rfl

theorem cell23_5290764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 2, 4, 2, 4].length) (baseStart_5290764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5290764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5290764 prefixEnd_5290764 := by exact prefixLift 5290764
  have htrace : WordTrace (prefixWord ++ tailWord_5290764) baseStart_5290764 baseEnd_5290764 := by
    simpa [prefixWord, tailWord_5290764, baseEnd_5290764] using wordTrace_append hprefix tailTrace_5290764
  have hstable : (prefixWord ++ tailWord_5290764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5290764).length < 2 ^ (prefixWord ++ tailWord_5290764).sum := by decide
  have hdescent : baseEnd_5290764 < baseStart_5290764 := by decide
  rcases family_descends (prefixWord ++ tailWord_5290764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5290785 : List Nat := [1, 2, 3, 2, 1, 2, 4, 2, 2, 2, 2]
def baseStart_5290785 : Nat := 118140960795 + 5290785 * 2 ^ 59
def prefixEnd_5290785 : Nat := 4983230072969 + 3 ^ 40 * 5290785 * 2
def baseEnd_5290785 : Nat := 2716715744598187513055629

theorem tailTrace_5290785 : CollatzResearch.WordTrace tailWord_5290785 prefixEnd_5290785 2716715744598187513055629 := by
  unfold tailWord_5290785
  simp only [CollatzResearch.WordTrace]
  refine ⟨192970782137397013984305809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128647188091598009322870539 192970782137397013984305809)
  ·
    refine ⟨144728086603047760488229357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192970782137397013984305809 144728086603047760488229357)
    ·
      refine ⟨54273032476142910183086009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 144728086603047760488229357 54273032476142910183086009)
      ·
        refine ⟨40704774357107182637314507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54273032476142910183086009 40704774357107182637314507)
        ·
          refine ⟨61057161535660773955971761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40704774357107182637314507 61057161535660773955971761)
          ·
            refine ⟨45792871151745580466978821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61057161535660773955971761 45792871151745580466978821)
            ·
              refine ⟨8586163340952296337558529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45792871151745580466978821 8586163340952296337558529)
              ·
                refine ⟨6439622505714222253168897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8586163340952296337558529 6439622505714222253168897)
                ·
                  refine ⟨4829716879285666689876673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6439622505714222253168897 4829716879285666689876673)
                  ·
                    refine ⟨3622287659464250017407505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4829716879285666689876673 3622287659464250017407505)
                    ·
                      refine ⟨2716715744598187513055629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3622287659464250017407505 2716715744598187513055629)
                      ·
                        rfl

theorem cell23_5290785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 4, 2, 2, 2, 2].length) (baseStart_5290785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5290785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5290785 prefixEnd_5290785 := by exact prefixLift 5290785
  have htrace : WordTrace (prefixWord ++ tailWord_5290785) baseStart_5290785 baseEnd_5290785 := by
    simpa [prefixWord, tailWord_5290785, baseEnd_5290785] using wordTrace_append hprefix tailTrace_5290785
  have hstable : (prefixWord ++ tailWord_5290785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5290785).length < 2 ^ (prefixWord ++ tailWord_5290785).sum := by decide
  have hdescent : baseEnd_5290785 < baseStart_5290785 := by decide
  rcases family_descends (prefixWord ++ tailWord_5290785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5290798 : List Nat := [4, 1, 3, 2, 1, 2, 1, 1, 2, 2, 4]
def baseStart_5290798 : Nat := 118140960795 + 5290798 * 2 ^ 59
def prefixEnd_5290798 : Nat := 4983230072969 + 3 ^ 40 * 5290798 * 2
def baseEnd_5290798 : Nat := 2716722419846695962193069

theorem tailTrace_5290798 : CollatzResearch.WordTrace tailWord_5290798 prefixEnd_5290798 2716722419846695962193069 := by
  unfold tailWord_5290798
  simp only [CollatzResearch.WordTrace]
  refine ⟨24121407035793739650566131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 128647504190899944803019365 24121407035793739650566131)
  ·
    refine ⟨36182110553690609475849197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24121407035793739650566131 36182110553690609475849197)
    ·
      refine ⟨13568291457633978553443449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36182110553690609475849197 13568291457633978553443449)
      ·
        refine ⟨10176218593225483915082587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13568291457633978553443449 10176218593225483915082587)
        ·
          refine ⟨15264327889838225872623881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10176218593225483915082587 15264327889838225872623881)
          ·
            refine ⟨11448245917378669404467911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15264327889838225872623881 11448245917378669404467911)
            ·
              refine ⟨17172368876068004106701867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11448245917378669404467911 17172368876068004106701867)
              ·
                refine ⟨25758553314102006160052801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17172368876068004106701867 25758553314102006160052801)
                ·
                  refine ⟨19318914985576504620039601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25758553314102006160052801 19318914985576504620039601)
                  ·
                    refine ⟨14489186239182378465029701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19318914985576504620039601 14489186239182378465029701)
                    ·
                      refine ⟨2716722419846695962193069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14489186239182378465029701 2716722419846695962193069)
                      ·
                        rfl

theorem cell23_5290798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 1, 1, 2, 2, 4].length) (baseStart_5290798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5290798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5290798 prefixEnd_5290798 := by exact prefixLift 5290798
  have htrace : WordTrace (prefixWord ++ tailWord_5290798) baseStart_5290798 baseEnd_5290798 := by
    simpa [prefixWord, tailWord_5290798, baseEnd_5290798] using wordTrace_append hprefix tailTrace_5290798
  have hstable : (prefixWord ++ tailWord_5290798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5290798).length < 2 ^ (prefixWord ++ tailWord_5290798).sum := by decide
  have hdescent : baseEnd_5290798 < baseStart_5290798 := by decide
  rcases family_descends (prefixWord ++ tailWord_5290798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5290801 : List Nat := [1, 2, 2, 3, 2, 1, 3, 1, 2, 3, 3]
def baseStart_5290801 : Nat := 118140960795 + 5290801 * 2 ^ 59
def prefixEnd_5290801 : Nat := 4983230072969 + 3 ^ 40 * 5290801 * 2
def baseEnd_5290801 : Nat := 2716723960288659450455555

theorem tailTrace_5290801 : CollatzResearch.WordTrace tailWord_5290801 prefixEnd_5290801 2716723960288659450455555 := by
  unfold tailWord_5290801
  simp only [CollatzResearch.WordTrace]
  refine ⟨192971365705339048716888257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128647577136892699144592171 192971365705339048716888257)
  ·
    refine ⟨144728524279004286537666193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192971365705339048716888257 144728524279004286537666193)
    ·
      refine ⟨108546393209253214903249645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144728524279004286537666193 108546393209253214903249645)
      ·
        refine ⟨40704897453469955588718617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 108546393209253214903249645 40704897453469955588718617)
        ·
          refine ⟨30528673090102466691538963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40704897453469955588718617 30528673090102466691538963)
          ·
            refine ⟨45793009635153700037308445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30528673090102466691538963 45793009635153700037308445)
            ·
              refine ⟨17172378613182637513990667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45793009635153700037308445 17172378613182637513990667)
              ·
                refine ⟨25758567919773956270986001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17172378613182637513990667 25758567919773956270986001)
                ·
                  refine ⟨19318925939830467203239501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25758567919773956270986001 19318925939830467203239501)
                  ·
                    refine ⟨7244597227436425201214813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19318925939830467203239501 7244597227436425201214813)
                    ·
                      refine ⟨2716723960288659450455555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7244597227436425201214813 2716723960288659450455555)
                      ·
                        rfl

theorem cell23_5290801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 3, 1, 2, 3, 3].length) (baseStart_5290801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5290801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5290801 prefixEnd_5290801 := by exact prefixLift 5290801
  have htrace : WordTrace (prefixWord ++ tailWord_5290801) baseStart_5290801 baseEnd_5290801 := by
    simpa [prefixWord, tailWord_5290801, baseEnd_5290801] using wordTrace_append hprefix tailTrace_5290801
  have hstable : (prefixWord ++ tailWord_5290801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5290801).length < 2 ^ (prefixWord ++ tailWord_5290801).sum := by decide
  have hdescent : baseEnd_5290801 < baseStart_5290801 := by decide
  rcases family_descends (prefixWord ++ tailWord_5290801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5290885 : List Nat := [1, 3, 1, 1, 3, 3, 3, 3, 1, 4]
def baseStart_5290885 : Nat := 118140960795 + 5290885 * 2 ^ 59
def prefixEnd_5290885 : Nat := 4983230072969 + 3 ^ 40 * 5290885 * 2
def baseEnd_5290885 : Nat := 905589030887879040601723

theorem tailTrace_5290885 : CollatzResearch.WordTrace tailWord_5290885 prefixEnd_5290885 905589030887879040601723 := by
  unfold tailWord_5290885
  simp only [CollatzResearch.WordTrace]
  refine ⟨192974429437034731062946109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128649619624689820708630739 192974429437034731062946109)
  ·
    refine ⟨72365411038888024148604791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 192974429437034731062946109 72365411038888024148604791)
    ·
      refine ⟨108548116558332036222907187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72365411038888024148604791 108548116558332036222907187)
      ·
        refine ⟨162822174837498054334360781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108548116558332036222907187 162822174837498054334360781)
        ·
          refine ⟨61058315564061770375385293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 162822174837498054334360781 61058315564061770375385293)
          ·
            refine ⟨22896868336523163890769485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61058315564061770375385293 22896868336523163890769485)
            ·
              refine ⟨8586325626196186459038557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22896868336523163890769485 8586325626196186459038557)
              ·
                refine ⟨3219872109823569922139459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8586325626196186459038557 3219872109823569922139459)
                ·
                  refine ⟨4829808164735354883209189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3219872109823569922139459 4829808164735354883209189)
                  ·
                    refine ⟨905589030887879040601723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4829808164735354883209189 905589030887879040601723)
                    ·
                      rfl

theorem cell23_5290885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 3, 3, 1, 4].length) (baseStart_5290885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5290885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5290885 prefixEnd_5290885 := by exact prefixLift 5290885
  have htrace : WordTrace (prefixWord ++ tailWord_5290885) baseStart_5290885 baseEnd_5290885 := by
    simpa [prefixWord, tailWord_5290885, baseEnd_5290885] using wordTrace_append hprefix tailTrace_5290885
  have hstable : (prefixWord ++ tailWord_5290885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5290885).length < 2 ^ (prefixWord ++ tailWord_5290885).sum := by decide
  have hdescent : baseEnd_5290885 < baseStart_5290885 := by decide
  rcases family_descends (prefixWord ++ tailWord_5290885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5290942 : List Nat := [4, 2, 1, 1, 1, 2, 2, 5, 1, 1, 3]
def baseStart_5290942 : Nat := 118140960795 + 5290942 * 2 ^ 59
def prefixEnd_5290942 : Nat := 4983230072969 + 3 ^ 40 * 5290942 * 2
def baseEnd_5290942 : Nat := 2716796361060943398792407

theorem tailTrace_5290942 : CollatzResearch.WordTrace tailWord_5290942 prefixEnd_5290942 2716796361060943398792407 := by
  unfold tailWord_5290942
  simp only [CollatzResearch.WordTrace]
  refine ⟨24122063549728528724721385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 128651005598552153198514053 24122063549728528724721385)
  ·
    refine ⟨18091547662296396543541039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24122063549728528724721385 18091547662296396543541039)
    ·
      refine ⟨27137321493444594815311559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18091547662296396543541039 27137321493444594815311559)
      ·
        refine ⟨40705982240166892222967339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27137321493444594815311559 40705982240166892222967339)
        ·
          refine ⟨61058973360250338334451009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40705982240166892222967339 61058973360250338334451009)
          ·
            refine ⟨45794230020187753750838257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61058973360250338334451009 45794230020187753750838257)
            ·
              refine ⟨34345672515140815313128693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45794230020187753750838257 34345672515140815313128693)
              ·
                refine ⟨3219906798294451435605815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34345672515140815313128693 3219906798294451435605815)
                ·
                  refine ⟨4829860197441677153408723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3219906798294451435605815 4829860197441677153408723)
                  ·
                    refine ⟨7244790296162515730113085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4829860197441677153408723 7244790296162515730113085)
                    ·
                      refine ⟨2716796361060943398792407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7244790296162515730113085 2716796361060943398792407)
                      ·
                        rfl

theorem cell23_5290942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 5, 1, 1, 3].length) (baseStart_5290942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5290942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5290942 prefixEnd_5290942 := by exact prefixLift 5290942
  have htrace : WordTrace (prefixWord ++ tailWord_5290942) baseStart_5290942 baseEnd_5290942 := by
    simpa [prefixWord, tailWord_5290942, baseEnd_5290942] using wordTrace_append hprefix tailTrace_5290942
  have hstable : (prefixWord ++ tailWord_5290942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5290942).length < 2 ^ (prefixWord ++ tailWord_5290942).sum := by decide
  have hdescent : baseEnd_5290942 < baseStart_5290942 := by decide
  rcases family_descends (prefixWord ++ tailWord_5290942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5290959 : List Nat := [1, 1, 2, 1, 1, 8, 2, 2, 1, 1, 3]
def baseStart_5290959 : Nat := 118140960795 + 5290959 * 2 ^ 59
def prefixEnd_5290959 : Nat := 4983230072969 + 3 ^ 40 * 5290959 * 2
def baseEnd_5290959 : Nat := 2716805090232069832279829

theorem tailTrace_5290959 : CollatzResearch.WordTrace tailWord_5290959 prefixEnd_5290959 2716805090232069832279829 := by
  unfold tailWord_5290959
  simp only [CollatzResearch.WordTrace]
  refine ⟨192977128438766641701139931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128651418959177761134093287 192977128438766641701139931)
  ·
    refine ⟨289465692658149962551709897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192977128438766641701139931 289465692658149962551709897)
    ·
      refine ⟨217099269493612471913782423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 289465692658149962551709897 217099269493612471913782423)
      ·
        refine ⟨325648904240418707870673635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 217099269493612471913782423 325648904240418707870673635)
        ·
          refine ⟨488473356360628061806010453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 325648904240418707870673635 488473356360628061806010453)
          ·
            refine ⟨5724297144851110099289185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 488473356360628061806010453 5724297144851110099289185)
            ·
              refine ⟨4293222858638332574466889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5724297144851110099289185 4293222858638332574466889)
              ·
                refine ⟨3219917143978749430850167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4293222858638332574466889 3219917143978749430850167)
                ·
                  refine ⟨4829875715968124146275251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3219917143978749430850167 4829875715968124146275251)
                  ·
                    refine ⟨7244813573952186219412877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4829875715968124146275251 7244813573952186219412877)
                    ·
                      refine ⟨2716805090232069832279829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7244813573952186219412877 2716805090232069832279829)
                      ·
                        rfl

theorem cell23_5290959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 2, 2, 1, 1, 3].length) (baseStart_5290959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5290959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5290959 prefixEnd_5290959 := by exact prefixLift 5290959
  have htrace : WordTrace (prefixWord ++ tailWord_5290959) baseStart_5290959 baseEnd_5290959 := by
    simpa [prefixWord, tailWord_5290959, baseEnd_5290959] using wordTrace_append hprefix tailTrace_5290959
  have hstable : (prefixWord ++ tailWord_5290959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5290959).length < 2 ^ (prefixWord ++ tailWord_5290959).sum := by decide
  have hdescent : baseEnd_5290959 < baseStart_5290959 := by decide
  rcases family_descends (prefixWord ++ tailWord_5290959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5290961 : List Nat := [1, 2, 2, 1, 2, 1, 3, 2, 3, 2, 4]
def baseStart_5290961 : Nat := 118140960795 + 5290961 * 2 ^ 59
def prefixEnd_5290961 : Nat := 4983230072969 + 3 ^ 40 * 5290961 * 2
def baseEnd_5290961 : Nat := 2716806117193378824454819

theorem tailTrace_5290961 : CollatzResearch.WordTrace tailWord_5290961 prefixEnd_5290961 2716806117193378824454819 := by
  unfold tailWord_5290961
  simp only [CollatzResearch.WordTrace]
  refine ⟨192977201384759396042712737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128651467589839597361808491 192977201384759396042712737)
  ·
    refine ⟨144732901038569547032034553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192977201384759396042712737 144732901038569547032034553)
    ·
      refine ⟨108549675778927160274025915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144732901038569547032034553 108549675778927160274025915)
      ·
        refine ⟨162824513668390740411038873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108549675778927160274025915 162824513668390740411038873)
        ·
          refine ⟨122118385251293055308279155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 162824513668390740411038873 122118385251293055308279155)
          ·
            refine ⟨183177577876939582962418733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122118385251293055308279155 183177577876939582962418733)
            ·
              refine ⟨68691591703852343610907025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 183177577876939582962418733 68691591703852343610907025)
              ·
                refine ⟨51518693777889257708180269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68691591703852343610907025 51518693777889257708180269)
                ·
                  refine ⟨19319510166708471640567601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51518693777889257708180269 19319510166708471640567601)
                  ·
                    refine ⟨14489632625031353730425701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19319510166708471640567601 14489632625031353730425701)
                    ·
                      refine ⟨2716806117193378824454819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14489632625031353730425701 2716806117193378824454819)
                      ·
                        rfl

theorem cell23_5290961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 2, 3, 2, 4].length) (baseStart_5290961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5290961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5290961 prefixEnd_5290961 := by exact prefixLift 5290961
  have htrace : WordTrace (prefixWord ++ tailWord_5290961) baseStart_5290961 baseEnd_5290961 := by
    simpa [prefixWord, tailWord_5290961, baseEnd_5290961] using wordTrace_append hprefix tailTrace_5290961
  have hstable : (prefixWord ++ tailWord_5290961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5290961).length < 2 ^ (prefixWord ++ tailWord_5290961).sum := by decide
  have hdescent : baseEnd_5290961 < baseStart_5290961 := by decide
  rcases family_descends (prefixWord ++ tailWord_5290961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5290968 : List Nat := [2, 1, 2, 2, 2, 3, 1, 2, 3, 2, 3]
def baseStart_5290968 : Nat := 118140960795 + 5290968 * 2 ^ 59
def prefixEnd_5290968 : Nat := 4983230072969 + 3 ^ 40 * 5290968 * 2
def baseEnd_5290968 : Nat := 2716809711557960297067287

theorem tailTrace_5290968 : CollatzResearch.WordTrace tailWord_5290968 prefixEnd_5290968 2716809711557960297067287 := by
  unfold tailWord_5290968
  simp only [CollatzResearch.WordTrace]
  refine ⟨96488728347867018119108779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128651637797156024158811705 96488728347867018119108779)
  ·
    refine ⟨144733092521800527178663169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96488728347867018119108779 144733092521800527178663169)
    ·
      refine ⟨108549819391350395383997377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144733092521800527178663169 108549819391350395383997377)
      ·
        refine ⟨81412364543512796537998033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108549819391350395383997377 81412364543512796537998033)
        ·
          refine ⟨61059273407634597403498525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81412364543512796537998033 61059273407634597403498525)
          ·
            refine ⟨22897227527862974026311947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61059273407634597403498525 22897227527862974026311947)
            ·
              refine ⟨34345841291794461039467921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22897227527862974026311947 34345841291794461039467921)
              ·
                refine ⟨25759380968845845779600941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34345841291794461039467921 25759380968845845779600941)
                ·
                  refine ⟨9659767863317192167350353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25759380968845845779600941 9659767863317192167350353)
                  ·
                    refine ⟨7244825897487894125512765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9659767863317192167350353 7244825897487894125512765)
                    ·
                      refine ⟨2716809711557960297067287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7244825897487894125512765 2716809711557960297067287)
                      ·
                        rfl

theorem cell23_5290968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 2, 3, 2, 3].length) (baseStart_5290968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5290968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5290968 prefixEnd_5290968 := by exact prefixLift 5290968
  have htrace : WordTrace (prefixWord ++ tailWord_5290968) baseStart_5290968 baseEnd_5290968 := by
    simpa [prefixWord, tailWord_5290968, baseEnd_5290968] using wordTrace_append hprefix tailTrace_5290968
  have hstable : (prefixWord ++ tailWord_5290968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5290968).length < 2 ^ (prefixWord ++ tailWord_5290968).sum := by decide
  have hdescent : baseEnd_5290968 < baseStart_5290968 := by decide
  rcases family_descends (prefixWord ++ tailWord_5290968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5290996 : List Nat := [2, 6, 2, 1, 1, 1, 1, 3, 1, 5]
def baseStart_5290996 : Nat := 118140960795 + 5290996 * 2 ^ 59
def prefixEnd_5290996 : Nat := 4983230072969 + 3 ^ 40 * 5290996 * 2
def baseEnd_5290996 : Nat := 905608029672095395839053

theorem tailTrace_5290996 : CollatzResearch.WordTrace tailWord_5290996 prefixEnd_5290996 905608029672095395839053 := by
  unfold tailWord_5290996
  simp only [CollatzResearch.WordTrace]
  refine ⟨96489238969816298510118421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128652318626421731346824561 96489238969816298510118421)
  ·
    refine ⟨4522933076710138992661801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 96489238969816298510118421 4522933076710138992661801)
    ·
      refine ⟨3392199807532604244496351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4522933076710138992661801 3392199807532604244496351)
      ·
        refine ⟨5088299711298906366744527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3392199807532604244496351 5088299711298906366744527)
        ·
          refine ⟨7632449566948359550116791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5088299711298906366744527 7632449566948359550116791)
          ·
            refine ⟨11448674350422539325175187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7632449566948359550116791 11448674350422539325175187)
            ·
              refine ⟨17173011525633808987762781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11448674350422539325175187 17173011525633808987762781)
              ·
                refine ⟨6439879322112678370411043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17173011525633808987762781 6439879322112678370411043)
                ·
                  refine ⟨9659818983169017555616565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6439879322112678370411043 9659818983169017555616565)
                  ·
                    refine ⟨905608029672095395839053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9659818983169017555616565 905608029672095395839053)
                    ·
                      rfl

theorem cell23_5290996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 1, 3, 1, 5].length) (baseStart_5290996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5290996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5290996 prefixEnd_5290996 := by exact prefixLift 5290996
  have htrace : WordTrace (prefixWord ++ tailWord_5290996) baseStart_5290996 baseEnd_5290996 := by
    simpa [prefixWord, tailWord_5290996, baseEnd_5290996] using wordTrace_append hprefix tailTrace_5290996
  have hstable : (prefixWord ++ tailWord_5290996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5290996).length < 2 ^ (prefixWord ++ tailWord_5290996).sum := by decide
  have hdescent : baseEnd_5290996 < baseStart_5290996 := by decide
  rcases family_descends (prefixWord ++ tailWord_5290996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5291015 : List Nat := [1, 1, 4, 3, 1, 1, 3, 1, 4, 1, 3]
def baseStart_5291015 : Nat := 118140960795 + 5291015 * 2 ^ 59
def prefixEnd_5291015 : Nat := 4983230072969 + 3 ^ 40 * 5291015 * 2
def baseEnd_5291015 : Nat := 2716833845148721613179571

theorem tailTrace_5291015 : CollatzResearch.WordTrace tailWord_5291015 prefixEnd_5291015 2716833845148721613179571 := by
  unfold tailWord_5291015
  simp only [CollatzResearch.WordTrace]
  refine ⟨192979170926563763265178499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128652780617709175510118999 192979170926563763265178499)
  ·
    refine ⟨289468756389845644897767749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192979170926563763265178499 289468756389845644897767749)
    ·
      refine ⟨54275391823096058418331453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 289468756389845644897767749 54275391823096058418331453)
      ·
        refine ⟨20353271933661021906874295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54275391823096058418331453 20353271933661021906874295)
        ·
          refine ⟨30529907900491532860311443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20353271933661021906874295 30529907900491532860311443)
          ·
            refine ⟨45794861850737299290467165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30529907900491532860311443 45794861850737299290467165)
            ·
              refine ⟨17173073194026487233925187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45794861850737299290467165 17173073194026487233925187)
              ·
                refine ⟨25759609791039730850887781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17173073194026487233925187 25759609791039730850887781)
                ·
                  refine ⟨4829926835819949534541459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25759609791039730850887781 4829926835819949534541459)
                  ·
                    refine ⟨7244890253729924301812189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4829926835819949534541459 7244890253729924301812189)
                    ·
                      refine ⟨2716833845148721613179571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7244890253729924301812189 2716833845148721613179571)
                      ·
                        rfl

theorem cell23_5291015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 3, 1, 4, 1, 3].length) (baseStart_5291015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5291015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5291015 prefixEnd_5291015 := by exact prefixLift 5291015
  have htrace : WordTrace (prefixWord ++ tailWord_5291015) baseStart_5291015 baseEnd_5291015 := by
    simpa [prefixWord, tailWord_5291015, baseEnd_5291015] using wordTrace_append hprefix tailTrace_5291015
  have hstable : (prefixWord ++ tailWord_5291015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5291015).length < 2 ^ (prefixWord ++ tailWord_5291015).sum := by decide
  have hdescent : baseEnd_5291015 < baseStart_5291015 := by decide
  rcases family_descends (prefixWord ++ tailWord_5291015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5291026 : List Nat := [3, 2, 5, 1, 2, 1, 1, 1, 1, 6]
def baseStart_5291026 : Nat := 118140960795 + 5291026 * 2 ^ 59
def prefixEnd_5291026 : Nat := 4983230072969 + 3 ^ 40 * 5291026 * 2
def baseEnd_5291026 : Nat := 905613164478640356714007

theorem tailTrace_5291026 : CollatzResearch.WordTrace tailWord_5291026 prefixEnd_5291026 905613164478640356714007 := by
  unfold tailWord_5291026
  simp only [CollatzResearch.WordTrace]
  refine ⟨48244893032380978035957233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128653048086349274762552621 48244893032380978035957233)
  ·
    refine ⟨36183669774285733526967925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48244893032380978035957233 36183669774285733526967925)
    ·
      refine ⟨3392219041339287518153243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 36183669774285733526967925 3392219041339287518153243)
      ·
        refine ⟨5088328562008931277229865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3392219041339287518153243 5088328562008931277229865)
        ·
          refine ⟨3816246421506698457922399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5088328562008931277229865 3816246421506698457922399)
          ·
            refine ⟨5724369632260047686883599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3816246421506698457922399 5724369632260047686883599)
            ·
              refine ⟨8586554448390071530325399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5724369632260047686883599 8586554448390071530325399)
              ·
                refine ⟨12879831672585107295488099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8586554448390071530325399 12879831672585107295488099)
                ·
                  refine ⟨19319747508877660943232149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12879831672585107295488099 19319747508877660943232149)
                  ·
                    refine ⟨905613164478640356714007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19319747508877660943232149 905613164478640356714007)
                    ·
                      rfl

theorem cell23_5291026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 1, 1, 1, 6].length) (baseStart_5291026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5291026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5291026 prefixEnd_5291026 := by exact prefixLift 5291026
  have htrace : WordTrace (prefixWord ++ tailWord_5291026) baseStart_5291026 baseEnd_5291026 := by
    simpa [prefixWord, tailWord_5291026, baseEnd_5291026] using wordTrace_append hprefix tailTrace_5291026
  have hstable : (prefixWord ++ tailWord_5291026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5291026).length < 2 ^ (prefixWord ++ tailWord_5291026).sum := by decide
  have hdescent : baseEnd_5291026 < baseStart_5291026 := by decide
  rcases family_descends (prefixWord ++ tailWord_5291026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5291042 : List Nat := [3, 3, 1, 1, 1, 3, 1, 4, 1, 3, 2]
def baseStart_5291042 : Nat := 118140960795 + 5291042 * 2 ^ 59
def prefixEnd_5291042 : Nat := 4983230072969 + 3 ^ 40 * 5291042 * 2
def baseEnd_5291042 : Nat := 2716847709126393007541947

theorem tailTrace_5291042 : CollatzResearch.WordTrace tailWord_5291042 prefixEnd_5291042 2716847709126393007541947 := by
  unfold tailWord_5291042
  simp only [CollatzResearch.WordTrace]
  refine ⟨48245038924366486719102845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128653437131643964584274253 48245038924366486719102845)
  ·
    refine ⟨18091889596637432519663567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48245038924366486719102845 18091889596637432519663567)
    ·
      refine ⟨27137834394956148779495351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18091889596637432519663567 27137834394956148779495351)
      ·
        refine ⟨40706751592434223169243027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27137834394956148779495351 40706751592434223169243027)
        ·
          refine ⟨61060127388651334753864541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40706751592434223169243027 61060127388651334753864541)
          ·
            refine ⟨22897547770744250532699203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61060127388651334753864541 22897547770744250532699203)
            ·
              refine ⟨34346321656116375799048805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22897547770744250532699203 34346321656116375799048805)
              ·
                refine ⟨6439935310521820462321651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34346321656116375799048805 6439935310521820462321651)
                ·
                  refine ⟨9659902965782730693482477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6439935310521820462321651 9659902965782730693482477)
                  ·
                    refine ⟨3622463612168524010055929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9659902965782730693482477 3622463612168524010055929)
                    ·
                      refine ⟨2716847709126393007541947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3622463612168524010055929 2716847709126393007541947)
                      ·
                        rfl

theorem cell23_5291042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 4, 1, 3, 2].length) (baseStart_5291042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5291042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5291042 prefixEnd_5291042 := by exact prefixLift 5291042
  have htrace : WordTrace (prefixWord ++ tailWord_5291042) baseStart_5291042 baseEnd_5291042 := by
    simpa [prefixWord, tailWord_5291042, baseEnd_5291042] using wordTrace_append hprefix tailTrace_5291042
  have hstable : (prefixWord ++ tailWord_5291042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5291042).length < 2 ^ (prefixWord ++ tailWord_5291042).sum := by decide
  have hdescent : baseEnd_5291042 < baseStart_5291042 := by decide
  rcases family_descends (prefixWord ++ tailWord_5291042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5291058 : List Nat := [3, 2, 1, 1, 2, 2, 3, 1, 2, 1, 5]
def baseStart_5291058 : Nat := 118140960795 + 5291058 * 2 ^ 59
def prefixEnd_5291058 : Nat := 4983230072969 + 3 ^ 40 * 5291058 * 2
def baseEnd_5291058 : Nat := 2716855924816864944941873

theorem tailTrace_5291058 : CollatzResearch.WordTrace tailWord_5291058 prefixEnd_5291058 2716855924816864944941873 := by
  unfold tailWord_5291058
  simp only [CollatzResearch.WordTrace]
  refine ⟨48245184816351995402248457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128653826176938654405995885 48245184816351995402248457)
  ·
    refine ⟨36183888612263996551686343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48245184816351995402248457 36183888612263996551686343)
    ·
      refine ⟨54275832918395994827529515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36183888612263996551686343 54275832918395994827529515)
      ·
        refine ⟨81413749377593992241294273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54275832918395994827529515 81413749377593992241294273)
        ·
          refine ⟨61060312033195494180970705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81413749377593992241294273 61060312033195494180970705)
          ·
            refine ⟨45795234024896620635728029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61060312033195494180970705 45795234024896620635728029)
            ·
              refine ⟨17173212759336232738398011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45795234024896620635728029 17173212759336232738398011)
              ·
                refine ⟨25759819139004349107597017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17173212759336232738398011 25759819139004349107597017)
                ·
                  refine ⟨19319864354253261830697763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25759819139004349107597017 19319864354253261830697763)
                  ·
                    refine ⟨28979796531379892746046645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19319864354253261830697763 28979796531379892746046645)
                    ·
                      refine ⟨2716855924816864944941873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28979796531379892746046645 2716855924816864944941873)
                      ·
                        rfl

theorem cell23_5291058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 3, 1, 2, 1, 5].length) (baseStart_5291058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5291058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5291058 prefixEnd_5291058 := by exact prefixLift 5291058
  have htrace : WordTrace (prefixWord ++ tailWord_5291058) baseStart_5291058 baseEnd_5291058 := by
    simpa [prefixWord, tailWord_5291058, baseEnd_5291058] using wordTrace_append hprefix tailTrace_5291058
  have hstable : (prefixWord ++ tailWord_5291058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5291058).length < 2 ^ (prefixWord ++ tailWord_5291058).sum := by decide
  have hdescent : baseEnd_5291058 < baseStart_5291058 := by decide
  rcases family_descends (prefixWord ++ tailWord_5291058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5291071 : List Nat := [1, 1, 2, 2, 3, 1, 1, 1, 1, 1, 9]
def baseStart_5291071 : Nat := 118140960795 + 5291071 * 2 ^ 59
def prefixEnd_5291071 : Nat := 4983230072969 + 3 ^ 40 * 5291071 * 2
def baseEnd_5291071 : Nat := 2716862600065373394079313

theorem tailTrace_5291071 : CollatzResearch.WordTrace tailWord_5291071 prefixEnd_5291071 2716862600065373394079313 := by
  unfold tailWord_5291071
  simp only [CollatzResearch.WordTrace]
  refine ⟨192981213414360884829217067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128654142276240589886144711 192981213414360884829217067)
  ·
    refine ⟨289471820121541327243825601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192981213414360884829217067 289471820121541327243825601)
    ·
      refine ⟨217103865091155995432869201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 289471820121541327243825601 217103865091155995432869201)
      ·
        refine ⟨162827898818366996574651901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 217103865091155995432869201 162827898818366996574651901)
        ·
          refine ⟨61060462056887623715494463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 162827898818366996574651901 61060462056887623715494463)
          ·
            refine ⟨91590693085331435573241695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61060462056887623715494463 91590693085331435573241695)
            ·
              refine ⟨137386039627997153359862543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91590693085331435573241695 137386039627997153359862543)
              ·
                refine ⟨206079059441995730039793815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 137386039627997153359862543 206079059441995730039793815)
                ·
                  refine ⟨309118589162993595059690723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 206079059441995730039793815 309118589162993595059690723)
                  ·
                    refine ⟨463677883744490392589536085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 309118589162993595059690723 463677883744490392589536085)
                    ·
                      refine ⟨2716862600065373394079313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 463677883744490392589536085 2716862600065373394079313)
                      ·
                        rfl

theorem cell23_5291071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 1, 1, 1, 9].length) (baseStart_5291071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5291071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5291071 prefixEnd_5291071 := by exact prefixLift 5291071
  have htrace : WordTrace (prefixWord ++ tailWord_5291071) baseStart_5291071 baseEnd_5291071 := by
    simpa [prefixWord, tailWord_5291071, baseEnd_5291071] using wordTrace_append hprefix tailTrace_5291071
  have hstable : (prefixWord ++ tailWord_5291071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5291071).length < 2 ^ (prefixWord ++ tailWord_5291071).sum := by decide
  have hdescent : baseEnd_5291071 < baseStart_5291071 := by decide
  rcases family_descends (prefixWord ++ tailWord_5291071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5291072 : List Nat := [2, 1, 1, 2, 2, 3, 2, 4, 2, 2, 2]
def baseStart_5291072 : Nat := 118140960795 + 5291072 * 2 ^ 59
def prefixEnd_5291072 : Nat := 4983230072969 + 3 ^ 40 * 5291072 * 2
def baseEnd_5291072 : Nat := 2716863113546027890166809

theorem tailTrace_5291072 : CollatzResearch.WordTrace tailWord_5291072 prefixEnd_5291072 2716863113546027890166809 := by
  unfold tailWord_5291072
  simp only [CollatzResearch.WordTrace]
  refine ⟨96490624943678631000001735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128654166591571508000002313 96490624943678631000001735)
  ·
    refine ⟨144735937415517946500002603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96490624943678631000001735 144735937415517946500002603)
    ·
      refine ⟨217103906123276919750003905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144735937415517946500002603 217103906123276919750003905)
      ·
        refine ⟨162827929592457689812502929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 217103906123276919750003905 162827929592457689812502929)
        ·
          refine ⟨122120947194343267359377197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 162827929592457689812502929 122120947194343267359377197)
          ·
            refine ⟨45795355197878725259766449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 122120947194343267359377197 45795355197878725259766449)
            ·
              refine ⟨34346516398409043944824837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45795355197878725259766449 34346516398409043944824837)
              ·
                refine ⟨6439971824701695739654657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34346516398409043944824837 6439971824701695739654657)
                ·
                  refine ⟨4829978868526271804740993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6439971824701695739654657 4829978868526271804740993)
                  ·
                    refine ⟨3622484151394703853555745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4829978868526271804740993 3622484151394703853555745)
                    ·
                      refine ⟨2716863113546027890166809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3622484151394703853555745 2716863113546027890166809)
                      ·
                        rfl

theorem cell23_5291072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 4, 2, 2, 2].length) (baseStart_5291072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5291072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5291072 prefixEnd_5291072 := by exact prefixLift 5291072
  have htrace : WordTrace (prefixWord ++ tailWord_5291072) baseStart_5291072 baseEnd_5291072 := by
    simpa [prefixWord, tailWord_5291072, baseEnd_5291072] using wordTrace_append hprefix tailTrace_5291072
  have hstable : (prefixWord ++ tailWord_5291072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5291072).length < 2 ^ (prefixWord ++ tailWord_5291072).sum := by decide
  have hdescent : baseEnd_5291072 < baseStart_5291072 := by decide
  rcases family_descends (prefixWord ++ tailWord_5291072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5291081 : List Nat := [1, 2, 1, 1, 2, 2, 2, 1, 2, 1, 8]
def baseStart_5291081 : Nat := 118140960795 + 5291081 * 2 ^ 59
def prefixEnd_5291081 : Nat := 4983230072969 + 3 ^ 40 * 5291081 * 2
def baseEnd_5291081 : Nat := 2716867734871918354954267

theorem tailTrace_5291081 : CollatzResearch.WordTrace tailWord_5291081 prefixEnd_5291081 2716867734871918354954267 := by
  unfold tailWord_5291081
  simp only [CollatzResearch.WordTrace]
  refine ⟨192981578144324656537081097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128654385429549771024720731 192981578144324656537081097)
  ·
    refine ⟨144736183608243492402810823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192981578144324656537081097 144736183608243492402810823)
    ·
      refine ⟨217104275412365238604216235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144736183608243492402810823 217104275412365238604216235)
      ·
        refine ⟨325656413118547857906324353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 217104275412365238604216235 325656413118547857906324353)
        ·
          refine ⟨244242309838910893429743265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 325656413118547857906324353 244242309838910893429743265)
          ·
            refine ⟨183181732379183170072307449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 244242309838910893429743265 183181732379183170072307449)
            ·
              refine ⟨137386299284387377554230587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 183181732379183170072307449 137386299284387377554230587)
              ·
                refine ⟨206079448926581066331345881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 137386299284387377554230587 206079448926581066331345881)
                ·
                  refine ⟨154559586694935799748509411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 206079448926581066331345881 154559586694935799748509411)
                  ·
                    refine ⟨231839380042403699622764117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 154559586694935799748509411 231839380042403699622764117)
                    ·
                      refine ⟨2716867734871918354954267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 231839380042403699622764117 2716867734871918354954267)
                      ·
                        rfl

theorem cell23_5291081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 1, 2, 1, 8].length) (baseStart_5291081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5291081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5291081 prefixEnd_5291081 := by exact prefixLift 5291081
  have htrace : WordTrace (prefixWord ++ tailWord_5291081) baseStart_5291081 baseEnd_5291081 := by
    simpa [prefixWord, tailWord_5291081, baseEnd_5291081] using wordTrace_append hprefix tailTrace_5291081
  have hstable : (prefixWord ++ tailWord_5291081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5291081).length < 2 ^ (prefixWord ++ tailWord_5291081).sum := by decide
  have hdescent : baseEnd_5291081 < baseStart_5291081 := by decide
  rcases family_descends (prefixWord ++ tailWord_5291081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5291088 : List Nat := [2, 1, 1, 1, 1, 3, 1, 5, 2, 3, 3]
def baseStart_5291088 : Nat := 118140960795 + 5291088 * 2 ^ 59
def prefixEnd_5291088 : Nat := 4983230072969 + 3 ^ 40 * 5291088 * 2
def baseEnd_5291088 : Nat := 2716871329236499827566735

theorem tailTrace_5291088 : CollatzResearch.WordTrace tailWord_5291088 prefixEnd_5291088 2716871329236499827566735 := by
  unfold tailWord_5291088
  simp only [CollatzResearch.WordTrace]
  refine ⟨96490916727649648366292959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128654555636866197821723945 96490916727649648366292959)
  ·
    refine ⟨144736375091474472549439439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96490916727649648366292959 144736375091474472549439439)
    ·
      refine ⟨217104562637211708824159159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144736375091474472549439439 217104562637211708824159159)
      ·
        refine ⟨325656843955817563236238739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 217104562637211708824159159 325656843955817563236238739)
        ·
          refine ⟨488485265933726344854358109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 325656843955817563236238739 488485265933726344854358109)
          ·
            refine ⟨183181974725147379320384291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 488485265933726344854358109 183181974725147379320384291)
            ·
              refine ⟨274772962087721068980576437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 183181974725147379320384291 274772962087721068980576437)
              ·
                refine ⟨25759965195723850216929041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 274772962087721068980576437 25759965195723850216929041)
                ·
                  refine ⟨19319973896792887662696781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25759965195723850216929041 19319973896792887662696781)
                  ·
                    refine ⟨7244990211297332873511293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19319973896792887662696781 7244990211297332873511293)
                    ·
                      refine ⟨2716871329236499827566735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7244990211297332873511293 2716871329236499827566735)
                      ·
                        rfl

theorem cell23_5291088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 5, 2, 3, 3].length) (baseStart_5291088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5291088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5291088 prefixEnd_5291088 := by exact prefixLift 5291088
  have htrace : WordTrace (prefixWord ++ tailWord_5291088) baseStart_5291088 baseEnd_5291088 := by
    simpa [prefixWord, tailWord_5291088, baseEnd_5291088] using wordTrace_append hprefix tailTrace_5291088
  have hstable : (prefixWord ++ tailWord_5291088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5291088).length < 2 ^ (prefixWord ++ tailWord_5291088).sum := by decide
  have hdescent : baseEnd_5291088 < baseStart_5291088 := by decide
  rcases family_descends (prefixWord ++ tailWord_5291088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5291089 : List Nat := [1, 2, 2, 1, 3, 1, 6, 1, 2, 2, 2]
def baseStart_5291089 : Nat := 118140960795 + 5291089 * 2 ^ 59
def prefixEnd_5291089 : Nat := 4983230072969 + 3 ^ 40 * 5291089 * 2
def baseEnd_5291089 : Nat := 2716871842717154323654231

theorem tailTrace_5291089 : CollatzResearch.WordTrace tailWord_5291089 prefixEnd_5291089 2716871842717154323654231 := by
  unfold tailWord_5291089
  simp only [CollatzResearch.WordTrace]
  refine ⟨192981869928295673903372321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128654579952197115935581547 192981869928295673903372321)
  ·
    refine ⟨144736402446221755427529241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192981869928295673903372321 144736402446221755427529241)
    ·
      refine ⟨108552301834666316570646931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144736402446221755427529241 108552301834666316570646931)
      ·
        refine ⟨162828452751999474855970397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108552301834666316570646931 162828452751999474855970397)
        ·
          refine ⟨61060669781999803070988899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 162828452751999474855970397 61060669781999803070988899)
          ·
            refine ⟨91591004672999704606483349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61060669781999803070988899 91591004672999704606483349)
            ·
              refine ⟨4293328344046861153428907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 91591004672999704606483349 4293328344046861153428907)
              ·
                refine ⟨6439992516070291730143361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4293328344046861153428907 6439992516070291730143361)
                ·
                  refine ⟨4829994387052718797607521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6439992516070291730143361 4829994387052718797607521)
                  ·
                    refine ⟨3622495790289539098205641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4829994387052718797607521 3622495790289539098205641)
                    ·
                      refine ⟨2716871842717154323654231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3622495790289539098205641 2716871842717154323654231)
                      ·
                        rfl

theorem cell23_5291089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 6, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 6, 1, 2, 2, 2].length) (baseStart_5291089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5291089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5291089 prefixEnd_5291089 := by exact prefixLift 5291089
  have htrace : WordTrace (prefixWord ++ tailWord_5291089) baseStart_5291089 baseEnd_5291089 := by
    simpa [prefixWord, tailWord_5291089, baseEnd_5291089] using wordTrace_append hprefix tailTrace_5291089
  have hstable : (prefixWord ++ tailWord_5291089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5291089).length < 2 ^ (prefixWord ++ tailWord_5291089).sum := by decide
  have hdescent : baseEnd_5291089 < baseStart_5291089 := by decide
  rcases family_descends (prefixWord ++ tailWord_5291089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5291129 : List Nat := [1, 2, 1, 3, 5, 2, 2, 2, 5]
def baseStart_5291129 : Nat := 118140960795 + 5291129 * 2 ^ 59
def prefixEnd_5291129 : Nat := 4983230072969 + 3 ^ 40 * 5291129 * 2
def baseEnd_5291129 : Nat := 301876931327037129683783

theorem tailTrace_5291129 : CollatzResearch.WordTrace tailWord_5291129 prefixEnd_5291129 301876931327037129683783 := by
  unfold tailWord_5291129
  simp only [CollatzResearch.WordTrace]
  refine ⟨192983328848150760734828441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128655552565433840489885627 192983328848150760734828441)
  ·
    refine ⟨144737496636113070551121331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192983328848150760734828441 144737496636113070551121331)
    ·
      refine ⟨217106244954169605826681997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144737496636113070551121331 217106244954169605826681997)
      ·
        refine ⟨81414841857813602185005749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 217106244954169605826681997 81414841857813602185005749)
        ·
          refine ⟨7632641424170025204844289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 81414841857813602185005749 7632641424170025204844289)
          ·
            refine ⟨5724481068127518903633217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7632641424170025204844289 5724481068127518903633217)
            ·
              refine ⟨4293360801095639177724913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5724481068127518903633217 4293360801095639177724913)
              ·
                refine ⟨3220020600821729383293685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4293360801095639177724913 3220020600821729383293685)
                ·
                  refine ⟨301876931327037129683783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3220020600821729383293685 301876931327037129683783)
                  ·
                    rfl

theorem cell23_5291129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 2, 2, 5].length) (baseStart_5291129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5291129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5291129 prefixEnd_5291129 := by exact prefixLift 5291129
  have htrace : WordTrace (prefixWord ++ tailWord_5291129) baseStart_5291129 baseEnd_5291129 := by
    simpa [prefixWord, tailWord_5291129, baseEnd_5291129] using wordTrace_append hprefix tailTrace_5291129
  have hstable : (prefixWord ++ tailWord_5291129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5291129).length < 2 ^ (prefixWord ++ tailWord_5291129).sum := by decide
  have hdescent : baseEnd_5291129 < baseStart_5291129 := by decide
  rcases family_descends (prefixWord ++ tailWord_5291129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5291145 : List Nat := [1, 2, 1, 1, 4, 3, 1, 1, 1, 6, 2]
def baseStart_5291145 : Nat := 118140960795 + 5291145 * 2 ^ 59
def prefixEnd_5291145 : Nat := 4983230072969 + 3 ^ 40 * 5291145 * 2
def baseEnd_5291145 : Nat := 2716900597633806104553973

theorem tailTrace_5291145 : CollatzResearch.WordTrace tailWord_5291145 prefixEnd_5291145 2716900597633806104553973 := by
  unfold tailWord_5291145
  simp only [CollatzResearch.WordTrace]
  refine ⟨192983912416092795467410889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128655941610728530311607259 192983912416092795467410889)
  ·
    refine ⟨144737934312069596600558167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192983912416092795467410889 144737934312069596600558167)
    ·
      refine ⟨217106901468104394900837251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144737934312069596600558167 217106901468104394900837251)
      ·
        refine ⟨325660352202156592351255877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 217106901468104394900837251 325660352202156592351255877)
        ·
          refine ⟨61061316037904361065860477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 325660352202156592351255877 61061316037904361065860477)
          ·
            refine ⟨22897993514214135399697679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61061316037904361065860477 22897993514214135399697679)
            ·
              refine ⟨34346990271321203099546519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22897993514214135399697679 34346990271321203099546519)
              ·
                refine ⟨51520485406981804649319779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34346990271321203099546519 51520485406981804649319779)
                ·
                  refine ⟨77280728110472706973979669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51520485406981804649319779 77280728110472706973979669)
                  ·
                    refine ⟨3622534130178408139405297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 77280728110472706973979669 3622534130178408139405297)
                    ·
                      refine ⟨2716900597633806104553973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3622534130178408139405297 2716900597633806104553973)
                      ·
                        rfl

theorem cell23_5291145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 1, 1, 6, 2].length) (baseStart_5291145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5291145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5291145 prefixEnd_5291145 := by exact prefixLift 5291145
  have htrace : WordTrace (prefixWord ++ tailWord_5291145) baseStart_5291145 baseEnd_5291145 := by
    simpa [prefixWord, tailWord_5291145, baseEnd_5291145] using wordTrace_append hprefix tailTrace_5291145
  have hstable : (prefixWord ++ tailWord_5291145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5291145).length < 2 ^ (prefixWord ++ tailWord_5291145).sum := by decide
  have hdescent : baseEnd_5291145 < baseStart_5291145 := by decide
  rcases family_descends (prefixWord ++ tailWord_5291145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5291162 : List Nat := [3, 1, 1, 5, 1, 1, 3, 1, 2, 1, 4]
def baseStart_5291162 : Nat := 118140960795 + 5291162 * 2 ^ 59
def prefixEnd_5291162 : Nat := 4983230072969 + 3 ^ 40 * 5291162 * 2
def baseEnd_5291162 : Nat := 2716909326804932538041395

theorem tailTrace_5291162 : CollatzResearch.WordTrace tailWord_5291162 prefixEnd_5291162 2716909326804932538041395 := by
  unfold tailWord_5291162
  simp only [CollatzResearch.WordTrace]
  refine ⟨48246133114257801842694935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128656354971354138247186493 48246133114257801842694935)
  ·
    refine ⟨72369199671386702764042403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48246133114257801842694935 72369199671386702764042403)
    ·
      refine ⟨108553799507080054146063605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72369199671386702764042403 108553799507080054146063605)
      ·
        refine ⟨10176918703788755076193463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 108553799507080054146063605 10176918703788755076193463)
        ·
          refine ⟨15265378055683132614290195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10176918703788755076193463 15265378055683132614290195)
          ·
            refine ⟨22898067083524698921435293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15265378055683132614290195 22898067083524698921435293)
            ·
              refine ⟨8586775156321762095538235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22898067083524698921435293 8586775156321762095538235)
              ·
                refine ⟨12880162734482643143307353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8586775156321762095538235 12880162734482643143307353)
                ·
                  refine ⟨9660122050861982357480515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12880162734482643143307353 9660122050861982357480515)
                  ·
                    refine ⟨14490183076292973536220773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9660122050861982357480515 14490183076292973536220773)
                    ·
                      refine ⟨2716909326804932538041395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14490183076292973536220773 2716909326804932538041395)
                      ·
                        rfl

theorem cell23_5291162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 3, 1, 2, 1, 4].length) (baseStart_5291162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5291162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5291162 prefixEnd_5291162 := by exact prefixLift 5291162
  have htrace : WordTrace (prefixWord ++ tailWord_5291162) baseStart_5291162 baseEnd_5291162 := by
    simpa [prefixWord, tailWord_5291162, baseEnd_5291162] using wordTrace_append hprefix tailTrace_5291162
  have hstable : (prefixWord ++ tailWord_5291162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5291162).length < 2 ^ (prefixWord ++ tailWord_5291162).sum := by decide
  have hdescent : baseEnd_5291162 < baseStart_5291162 := by decide
  rcases family_descends (prefixWord ++ tailWord_5291162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5291165 : List Nat := [1, 4, 2, 1, 1, 2, 3, 1, 1, 4, 3]
def baseStart_5291165 : Nat := 118140960795 + 5291165 * 2 ^ 59
def prefixEnd_5291165 : Nat := 4983230072969 + 3 ^ 40 * 5291165 * 2
def baseEnd_5291165 : Nat := 2716910867246896026303881

theorem tailTrace_5291165 : CollatzResearch.WordTrace tailWord_5291165 prefixEnd_5291165 2716910867246896026303881 := by
  unfold tailWord_5291165
  simp only [CollatzResearch.WordTrace]
  refine ⟨192984641876020338883138949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128656427917346892588759299 192984641876020338883138949)
  ·
    refine ⟨36184620351753813540588553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 192984641876020338883138949 36184620351753813540588553)
    ·
      refine ⟨27138465263815360155441415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36184620351753813540588553 27138465263815360155441415)
      ·
        refine ⟨40707697895723040233162123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27138465263815360155441415 40707697895723040233162123)
        ·
          refine ⟨61061546843584560349743185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40707697895723040233162123 61061546843584560349743185)
          ·
            refine ⟨45796160132688420262307389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61061546843584560349743185 45796160132688420262307389)
            ·
              refine ⟨17173560049758157598365271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45796160132688420262307389 17173560049758157598365271)
              ·
                refine ⟨25760340074637236397547907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17173560049758157598365271 25760340074637236397547907)
                ·
                  refine ⟨38640510111955854596321861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25760340074637236397547907 38640510111955854596321861)
                  ·
                    refine ⟨7245095645991722736810349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 38640510111955854596321861 7245095645991722736810349)
                    ·
                      refine ⟨2716910867246896026303881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7245095645991722736810349 2716910867246896026303881)
                      ·
                        rfl

theorem cell23_5291165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 3, 1, 1, 4, 3].length) (baseStart_5291165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5291165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5291165 prefixEnd_5291165 := by exact prefixLift 5291165
  have htrace : WordTrace (prefixWord ++ tailWord_5291165) baseStart_5291165 baseEnd_5291165 := by
    simpa [prefixWord, tailWord_5291165, baseEnd_5291165] using wordTrace_append hprefix tailTrace_5291165
  have hstable : (prefixWord ++ tailWord_5291165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5291165).length < 2 ^ (prefixWord ++ tailWord_5291165).sum := by decide
  have hdescent : baseEnd_5291165 < baseStart_5291165 := by decide
  rcases family_descends (prefixWord ++ tailWord_5291165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5291168 : List Nat := [2, 1, 1, 4, 2, 1, 2, 2, 8]
def baseStart_5291168 : Nat := 118140960795 + 5291168 * 2 ^ 59
def prefixEnd_5291168 : Nat := 4983230072969 + 3 ^ 40 * 5291168 * 2
def baseEnd_5291168 : Nat := 301879156409873279396263

theorem tailTrace_5291168 : CollatzResearch.WordTrace tailWord_5291168 prefixEnd_5291168 301879156409873279396263 := by
  unfold tailWord_5291168
  simp only [CollatzResearch.WordTrace]
  refine ⟨96492375647504735197749079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128656500863339646930332105 96492375647504735197749079)
  ·
    refine ⟨144738563471257102796623619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96492375647504735197749079 144738563471257102796623619)
    ·
      refine ⟨217107845206885654194935429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144738563471257102796623619 217107845206885654194935429)
      ·
        refine ⟨40707720976291060161550393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 217107845206885654194935429 40707720976291060161550393)
        ·
          refine ⟨30530790732218295121162795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40707720976291060161550393 30530790732218295121162795)
          ·
            refine ⟨45796186098327442681744193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30530790732218295121162795 45796186098327442681744193)
            ·
              refine ⟨34347139573745582011308145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45796186098327442681744193 34347139573745582011308145)
              ·
                refine ⟨25760354680309186508481109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34347139573745582011308145 25760354680309186508481109)
                ·
                  refine ⟨301879156409873279396263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25760354680309186508481109 301879156409873279396263)
                  ·
                    rfl

theorem cell23_5291168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 2, 8].length) (baseStart_5291168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5291168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5291168 prefixEnd_5291168 := by exact prefixLift 5291168
  have htrace : WordTrace (prefixWord ++ tailWord_5291168) baseStart_5291168 baseEnd_5291168 := by
    simpa [prefixWord, tailWord_5291168, baseEnd_5291168] using wordTrace_append hprefix tailTrace_5291168
  have hstable : (prefixWord ++ tailWord_5291168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5291168).length < 2 ^ (prefixWord ++ tailWord_5291168).sum := by decide
  have hdescent : baseEnd_5291168 < baseStart_5291168 := by decide
  rcases family_descends (prefixWord ++ tailWord_5291168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5291175 : List Nat := [1, 1, 6, 2, 1, 1, 1, 1, 2, 1, 6]
def baseStart_5291175 : Nat := 118140960795 + 5291175 * 2 ^ 59
def prefixEnd_5291175 : Nat := 4983230072969 + 3 ^ 40 * 5291175 * 2
def baseEnd_5291175 : Nat := 2716916002053440987178835

theorem tailTrace_5291175 : CollatzResearch.WordTrace tailWord_5291175 prefixEnd_5291175 2716916002053440987178835 := by
  unfold tailWord_5291175
  simp only [CollatzResearch.WordTrace]
  refine ⟨192985006605984110591002979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128656671070656073727335319 192985006605984110591002979)
  ·
    refine ⟨289477509908976165886504469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192985006605984110591002979 289477509908976165886504469)
    ·
      refine ⟨13569258276983257775929897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 289477509908976165886504469 13569258276983257775929897)
      ·
        refine ⟨10176943707737443331947423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13569258276983257775929897 10176943707737443331947423)
        ·
          refine ⟨15265415561606164997921135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10176943707737443331947423 15265415561606164997921135)
          ·
            refine ⟨22898123342409247496881703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15265415561606164997921135 22898123342409247496881703)
            ·
              refine ⟨34347185013613871245322555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22898123342409247496881703 34347185013613871245322555)
              ·
                refine ⟨51520777520420806867983833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34347185013613871245322555 51520777520420806867983833)
                ·
                  refine ⟨38640583140315605150987875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51520777520420806867983833 38640583140315605150987875)
                  ·
                    refine ⟨57960874710473407726481813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 38640583140315605150987875 57960874710473407726481813)
                    ·
                      refine ⟨2716916002053440987178835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 57960874710473407726481813 2716916002053440987178835)
                      ·
                        rfl

theorem cell23_5291175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 1, 2, 1, 6].length) (baseStart_5291175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5291175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5291175 prefixEnd_5291175 := by exact prefixLift 5291175
  have htrace : WordTrace (prefixWord ++ tailWord_5291175) baseStart_5291175 baseEnd_5291175 := by
    simpa [prefixWord, tailWord_5291175, baseEnd_5291175] using wordTrace_append hprefix tailTrace_5291175
  have hstable : (prefixWord ++ tailWord_5291175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5291175).length < 2 ^ (prefixWord ++ tailWord_5291175).sum := by decide
  have hdescent : baseEnd_5291175 < baseStart_5291175 := by decide
  rcases family_descends (prefixWord ++ tailWord_5291175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5291185 : List Nat := [1, 2, 2, 5, 1, 2, 1, 1, 8]
def baseStart_5291185 : Nat := 118140960795 + 5291185 * 2 ^ 59
def prefixEnd_5291185 : Nat := 4983230072969 + 3 ^ 40 * 5291185 * 2
def baseEnd_5291185 : Nat := 301880126317776216450421

theorem tailTrace_5291185 : CollatzResearch.WordTrace tailWord_5291185 prefixEnd_5291185 301880126317776216450421 := by
  unfold tailWord_5291185
  simp only [CollatzResearch.WordTrace]
  refine ⟨192985371335947882298867009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128656914223965254865911339 192985371335947882298867009)
  ·
    refine ⟨144739028501960911724150257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192985371335947882298867009 144739028501960911724150257)
    ·
      refine ⟨108554271376470683793112693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144739028501960911724150257 108554271376470683793112693)
      ·
        refine ⟨10176962941544126605604315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 108554271376470683793112693 10176962941544126605604315)
        ·
          refine ⟨15265444412316189908406473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10176962941544126605604315 15265444412316189908406473)
          ·
            refine ⟨11449083309237142431304855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15265444412316189908406473 11449083309237142431304855)
            ·
              refine ⟨17173624963855713646957283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11449083309237142431304855 17173624963855713646957283)
              ·
                refine ⟨25760437445783570470435925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17173624963855713646957283 25760437445783570470435925)
                ·
                  refine ⟨301880126317776216450421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25760437445783570470435925 301880126317776216450421)
                  ·
                    rfl

theorem cell23_5291185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 1, 1, 8].length) (baseStart_5291185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5291185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5291185 prefixEnd_5291185 := by exact prefixLift 5291185
  have htrace : WordTrace (prefixWord ++ tailWord_5291185) baseStart_5291185 baseEnd_5291185 := by
    simpa [prefixWord, tailWord_5291185, baseEnd_5291185] using wordTrace_append hprefix tailTrace_5291185
  have hstable : (prefixWord ++ tailWord_5291185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5291185).length < 2 ^ (prefixWord ++ tailWord_5291185).sum := by decide
  have hdescent : baseEnd_5291185 < baseStart_5291185 := by decide
  rcases family_descends (prefixWord ++ tailWord_5291185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5291208 : List Nat := [2, 1, 3, 1, 2, 1, 2, 1, 2, 1, 7]
def baseStart_5291208 : Nat := 118140960795 + 5291208 * 2 ^ 59
def prefixEnd_5291208 : Nat := 4983230072969 + 3 ^ 40 * 5291208 * 2
def baseEnd_5291208 : Nat := 2716932946915039358066183

theorem tailTrace_5291208 : CollatzResearch.WordTrace tailWord_5291208 prefixEnd_5291208 2716932946915039358066183 := by
  unfold tailWord_5291208
  simp only [CollatzResearch.WordTrace]
  refine ⟨96493105107432278613477139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128657473476576371484636185 96493105107432278613477139)
  ·
    refine ⟨144739657661148417920215709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96493105107432278613477139 144739657661148417920215709)
    ·
      refine ⟨54277371622930656720080891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 144739657661148417920215709 54277371622930656720080891)
      ·
        refine ⟨81416057434395985080121337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54277371622930656720080891 81416057434395985080121337)
        ·
          refine ⟨61062043075796988810091003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81416057434395985080121337 61062043075796988810091003)
          ·
            refine ⟨91593064613695483215136505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61062043075796988810091003 91593064613695483215136505)
            ·
              refine ⟨68694798460271612411352379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91593064613695483215136505 68694798460271612411352379)
              ·
                refine ⟨103042197690407418617028569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68694798460271612411352379 103042197690407418617028569)
                ·
                  refine ⟨77281648267805563962771427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 103042197690407418617028569 77281648267805563962771427)
                  ·
                    refine ⟨115922472401708345944157141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 77281648267805563962771427 115922472401708345944157141)
                    ·
                      refine ⟨2716932946915039358066183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 115922472401708345944157141 2716932946915039358066183)
                      ·
                        rfl

theorem cell23_5291208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 1, 2, 1, 7].length) (baseStart_5291208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5291208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5291208 prefixEnd_5291208 := by exact prefixLift 5291208
  have htrace : WordTrace (prefixWord ++ tailWord_5291208) baseStart_5291208 baseEnd_5291208 := by
    simpa [prefixWord, tailWord_5291208, baseEnd_5291208] using wordTrace_append hprefix tailTrace_5291208
  have hstable : (prefixWord ++ tailWord_5291208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5291208).length < 2 ^ (prefixWord ++ tailWord_5291208).sum := by decide
  have hdescent : baseEnd_5291208 < baseStart_5291208 := by decide
  rcases family_descends (prefixWord ++ tailWord_5291208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5291255 : List Nat := [1, 1, 3, 1, 1, 1, 2, 3, 5, 2, 3]
def baseStart_5291255 : Nat := 118140960795 + 5291255 * 2 ^ 59
def prefixEnd_5291255 : Nat := 4983230072969 + 3 ^ 40 * 5291255 * 2
def baseEnd_5291255 : Nat := 2716957080505800674178467

theorem tailTrace_5291255 : CollatzResearch.WordTrace tailWord_5291255 prefixEnd_5291255 2716957080505800674178467 := by
  unfold tailWord_5291255
  simp only [CollatzResearch.WordTrace]
  refine ⟨192987924445694284253915219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128658616297129522835943479 192987924445694284253915219)
  ·
    refine ⟨289481886668541426380872829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192987924445694284253915219 289481886668541426380872829)
    ·
      refine ⟨108555707500703034892827311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 289481886668541426380872829 108555707500703034892827311)
      ·
        refine ⟨162833561251054552339240967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108555707500703034892827311 162833561251054552339240967)
        ·
          refine ⟨244250341876581828508861451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162833561251054552339240967 244250341876581828508861451)
          ·
            refine ⟨366375512814872742763292177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 244250341876581828508861451 366375512814872742763292177)
            ·
              refine ⟨274781634611154557072469133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 366375512814872742763292177 274781634611154557072469133)
              ·
                refine ⟨103043112979182958902175925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 274781634611154557072469133 103043112979182958902175925)
                ·
                  refine ⟨9660291841798402397078993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 103043112979182958902175925 9660291841798402397078993)
                  ·
                    refine ⟨7245218881348801797809245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9660291841798402397078993 7245218881348801797809245)
                    ·
                      refine ⟨2716957080505800674178467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7245218881348801797809245 2716957080505800674178467)
                      ·
                        rfl

theorem cell23_5291255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 3, 5, 2, 3].length) (baseStart_5291255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5291255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5291255 prefixEnd_5291255 := by exact prefixLift 5291255
  have htrace : WordTrace (prefixWord ++ tailWord_5291255) baseStart_5291255 baseEnd_5291255 := by
    simpa [prefixWord, tailWord_5291255, baseEnd_5291255] using wordTrace_append hprefix tailTrace_5291255
  have hstable : (prefixWord ++ tailWord_5291255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5291255).length < 2 ^ (prefixWord ++ tailWord_5291255).sum := by decide
  have hdescent : baseEnd_5291255 < baseStart_5291255 := by decide
  rcases family_descends (prefixWord ++ tailWord_5291255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5291265 : List Nat := [1, 2, 4, 1, 1, 3, 2, 1, 1, 1, 6]
def baseStart_5291265 : Nat := 118140960795 + 5291265 * 2 ^ 59
def prefixEnd_5291265 : Nat := 4983230072969 + 3 ^ 40 * 5291265 * 2
def baseEnd_5291265 : Nat := 2716962215312345635053421

theorem tailTrace_5291265 : CollatzResearch.WordTrace tailWord_5291265 prefixEnd_5291265 2716962215312345635053421 := by
  unfold tailWord_5291265
  simp only [CollatzResearch.WordTrace]
  refine ⟨192988289175658055961779249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128658859450438703974519499 192988289175658055961779249)
  ·
    refine ⟨144741216881743541971334437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192988289175658055961779249 144741216881743541971334437)
    ·
      refine ⟨27138978165326914119625207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 144741216881743541971334437 27138978165326914119625207)
      ·
        refine ⟨40708467247990371179437811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27138978165326914119625207 40708467247990371179437811)
        ·
          refine ⟨61062700871985556769156717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40708467247990371179437811 61062700871985556769156717)
          ·
            refine ⟨22898512826994583788433769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61062700871985556769156717 22898512826994583788433769)
            ·
              refine ⟨17173884620245937841325327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22898512826994583788433769 17173884620245937841325327)
              ·
                refine ⟨25760826930368906761987991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17173884620245937841325327 25760826930368906761987991)
                ·
                  refine ⟨38641240395553360142981987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25760826930368906761987991 38641240395553360142981987)
                  ·
                    refine ⟨57961860593330040214472981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 38641240395553360142981987 57961860593330040214472981)
                    ·
                      refine ⟨2716962215312345635053421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 57961860593330040214472981 2716962215312345635053421)
                      ·
                        rfl

theorem cell23_5291265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 2, 1, 1, 1, 6].length) (baseStart_5291265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5291265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5291265 prefixEnd_5291265 := by exact prefixLift 5291265
  have htrace : WordTrace (prefixWord ++ tailWord_5291265) baseStart_5291265 baseEnd_5291265 := by
    simpa [prefixWord, tailWord_5291265, baseEnd_5291265] using wordTrace_append hprefix tailTrace_5291265
  have hstable : (prefixWord ++ tailWord_5291265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5291265).length < 2 ^ (prefixWord ++ tailWord_5291265).sum := by decide
  have hdescent : baseEnd_5291265 < baseStart_5291265 := by decide
  rcases family_descends (prefixWord ++ tailWord_5291265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5291266 : List Nat := [3, 4, 1, 1, 3, 2, 1, 2, 1, 5]
def baseStart_5291266 : Nat := 118140960795 + 5291266 * 2 ^ 59
def prefixEnd_5291266 : Nat := 4983230072969 + 3 ^ 40 * 5291266 * 2
def baseEnd_5291266 : Nat := 905654242931000043713639

theorem tailTrace_5291266 : CollatzResearch.WordTrace tailWord_5291266 prefixEnd_5291266 905654242931000043713639 := by
  unfold tailWord_5291266
  simp only [CollatzResearch.WordTrace]
  refine ⟨48247081412163608283141413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128658883765769622088377101 48247081412163608283141413)
  ·
    refine ⟨9046327764780676553089015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48247081412163608283141413 9046327764780676553089015)
    ·
      refine ⟨13569491647171014829633523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9046327764780676553089015 13569491647171014829633523)
      ·
        refine ⟨20354237470756522244450285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13569491647171014829633523 20354237470756522244450285)
        ·
          refine ⟨7632839051533695841668857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20354237470756522244450285 7632839051533695841668857)
          ·
            refine ⟨5724629288650271881251643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7632839051533695841668857 5724629288650271881251643)
            ·
              refine ⟨8586943932975407821877465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5724629288650271881251643 8586943932975407821877465)
              ·
                refine ⟨6440207949731555866408099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8586943932975407821877465 6440207949731555866408099)
                ·
                  refine ⟨9660311924597333799612149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6440207949731555866408099 9660311924597333799612149)
                  ·
                    refine ⟨905654242931000043713639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9660311924597333799612149 905654242931000043713639)
                    ·
                      rfl

theorem cell23_5291266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 1, 2, 1, 5].length) (baseStart_5291266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5291266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5291266 prefixEnd_5291266 := by exact prefixLift 5291266
  have htrace : WordTrace (prefixWord ++ tailWord_5291266) baseStart_5291266 baseEnd_5291266 := by
    simpa [prefixWord, tailWord_5291266, baseEnd_5291266] using wordTrace_append hprefix tailTrace_5291266
  have hstable : (prefixWord ++ tailWord_5291266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5291266).length < 2 ^ (prefixWord ++ tailWord_5291266).sum := by decide
  have hdescent : baseEnd_5291266 < baseStart_5291266 := by decide
  rcases family_descends (prefixWord ++ tailWord_5291266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5291309 : List Nat := [1, 5, 3, 1, 1, 3, 1, 8]
def baseStart_5291309 : Nat := 118140960795 + 5291309 * 2 ^ 59
def prefixEnd_5291309 : Nat := 4983230072969 + 3 ^ 40 * 5291309 * 2
def baseEnd_5291309 : Nat := 100629066980042350477897

theorem tailTrace_5291309 : CollatzResearch.WordTrace tailWord_5291309 prefixEnd_5291309 100629066980042350477897 := by
  unfold tailWord_5291309
  simp only [CollatzResearch.WordTrace]
  refine ⟨192989893987498651476380981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128659929324999100984253987 192989893987498651476380981)
  ·
    refine ⟨18092802561327998575910717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 192989893987498651476380981 18092802561327998575910717)
    ·
      refine ⟨6784800960497999465966519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18092802561327998575910717 6784800960497999465966519)
      ·
        refine ⟨10177201440746999198949779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6784800960497999465966519 10177201440746999198949779)
        ·
          refine ⟨15265802161120498798424669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10177201440746999198949779 15265802161120498798424669)
          ·
            refine ⟨5724675810420187049409251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15265802161120498798424669 5724675810420187049409251)
            ·
              refine ⟨8587013715630280574113877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5724675810420187049409251 8587013715630280574113877)
              ·
                refine ⟨100629066980042350477897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8587013715630280574113877 100629066980042350477897)
                ·
                  rfl

theorem cell23_5291309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 1, 8].length) (baseStart_5291309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5291309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5291309 prefixEnd_5291309 := by exact prefixLift 5291309
  have htrace : WordTrace (prefixWord ++ tailWord_5291309) baseStart_5291309 baseEnd_5291309 := by
    simpa [prefixWord, tailWord_5291309, baseEnd_5291309] using wordTrace_append hprefix tailTrace_5291309
  have hstable : (prefixWord ++ tailWord_5291309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5291309).length < 2 ^ (prefixWord ++ tailWord_5291309).sum := by decide
  have hdescent : baseEnd_5291309 < baseStart_5291309 := by decide
  rcases family_descends (prefixWord ++ tailWord_5291309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5291312 : List Nat := [2, 1, 1, 1, 2, 2, 3, 1, 5, 3, 2]
def baseStart_5291312 : Nat := 118140960795 + 5291312 * 2 ^ 59
def prefixEnd_5291312 : Nat := 4983230072969 + 3 ^ 40 * 5291312 * 2
def baseEnd_5291312 : Nat := 2716986348903106951165705

theorem tailTrace_5291312 : CollatzResearch.WordTrace tailWord_5291312 prefixEnd_5291312 2716986348903106951165705 := by
  unfold tailWord_5291312
  simp only [CollatzResearch.WordTrace]
  refine ⟨96495001703243891494370095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128660002270991855325826793 96495001703243891494370095)
  ·
    refine ⟨144742502554865837241555143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96495001703243891494370095 144742502554865837241555143)
    ·
      refine ⟨217113753832298755862332715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144742502554865837241555143 217113753832298755862332715)
      ·
        refine ⟨325670630748448133793499073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 217113753832298755862332715 325670630748448133793499073)
        ·
          refine ⟨244252973061336100345124305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 325670630748448133793499073 244252973061336100345124305)
          ·
            refine ⟨183189729796002075258843229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 244252973061336100345124305 183189729796002075258843229)
            ·
              refine ⟨68696148673500778222066211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 183189729796002075258843229 68696148673500778222066211)
              ·
                refine ⟨103044223010251167333099317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68696148673500778222066211 103044223010251167333099317)
                ·
                  refine ⟨9660395907211046937478061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 103044223010251167333099317 9660395907211046937478061)
                  ·
                    refine ⟨3622648465204142601554273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9660395907211046937478061 3622648465204142601554273)
                    ·
                      refine ⟨2716986348903106951165705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3622648465204142601554273 2716986348903106951165705)
                      ·
                        rfl

theorem cell23_5291312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 1, 5, 3, 2].length) (baseStart_5291312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5291312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5291312 prefixEnd_5291312 := by exact prefixLift 5291312
  have htrace : WordTrace (prefixWord ++ tailWord_5291312) baseStart_5291312 baseEnd_5291312 := by
    simpa [prefixWord, tailWord_5291312, baseEnd_5291312] using wordTrace_append hprefix tailTrace_5291312
  have hstable : (prefixWord ++ tailWord_5291312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5291312).length < 2 ^ (prefixWord ++ tailWord_5291312).sum := by decide
  have hdescent : baseEnd_5291312 < baseStart_5291312 := by decide
  rcases family_descends (prefixWord ++ tailWord_5291312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5291345 : List Nat := [1, 2, 2, 1, 4, 1, 2, 1, 1, 3, 5]
def baseStart_5291345 : Nat := 118140960795 + 5291345 * 2 ^ 59
def prefixEnd_5291345 : Nat := 4983230072969 + 3 ^ 40 * 5291345 * 2
def baseEnd_5291345 : Nat := 2717003293764705322053053

theorem tailTrace_5291345 : CollatzResearch.WordTrace tailWord_5291345 prefixEnd_5291345 2717003293764705322053053 := by
  unfold tailWord_5291345
  simp only [CollatzResearch.WordTrace]
  refine ⟨192991207015368229624691489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128660804676912153083127659 192991207015368229624691489)
  ·
    refine ⟨144743405261526172218518617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192991207015368229624691489 144743405261526172218518617)
    ·
      refine ⟨108557553946144629163888963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144743405261526172218518617 108557553946144629163888963)
      ·
        refine ⟨162836330919216943745833445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108557553946144629163888963 162836330919216943745833445)
        ·
          refine ⟨30531812047353176952343771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 162836330919216943745833445 30531812047353176952343771)
          ·
            refine ⟨45797718071029765428515657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30531812047353176952343771 45797718071029765428515657)
            ·
              refine ⟨34348288553272324071386743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45797718071029765428515657 34348288553272324071386743)
              ·
                refine ⟨51522432829908486107080115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34348288553272324071386743 51522432829908486107080115)
                ·
                  refine ⟨77283649244862729160620173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51522432829908486107080115 77283649244862729160620173)
                  ·
                    refine ⟨28981368466823523435232565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 77283649244862729160620173 28981368466823523435232565)
                    ·
                      refine ⟨2717003293764705322053053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28981368466823523435232565 2717003293764705322053053)
                      ·
                        rfl

theorem cell23_5291345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 1, 1, 3, 5].length) (baseStart_5291345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5291345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5291345 prefixEnd_5291345 := by exact prefixLift 5291345
  have htrace : WordTrace (prefixWord ++ tailWord_5291345) baseStart_5291345 baseEnd_5291345 := by
    simpa [prefixWord, tailWord_5291345, baseEnd_5291345] using wordTrace_append hprefix tailTrace_5291345
  have hstable : (prefixWord ++ tailWord_5291345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5291345).length < 2 ^ (prefixWord ++ tailWord_5291345).sum := by decide
  have hdescent : baseEnd_5291345 < baseStart_5291345 := by decide
  rcases family_descends (prefixWord ++ tailWord_5291345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5291372 : List Nat := [2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 4]
def baseStart_5291372 : Nat := 118140960795 + 5291372 * 2 ^ 59
def prefixEnd_5291372 : Nat := 4983230072969 + 3 ^ 40 * 5291372 * 2
def baseEnd_5291372 : Nat := 2717017157742376716415429

theorem tailTrace_5291372 : CollatzResearch.WordTrace tailWord_5291372 prefixEnd_5291372 2717017157742376716415429 := by
  unfold tailWord_5291372
  simp only [CollatzResearch.WordTrace]
  refine ⟨96496095893135206617962185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128661461190846942157282913 96496095893135206617962185)
  ·
    refine ⟨72372071919851404963471639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96496095893135206617962185 72372071919851404963471639)
    ·
      refine ⟨108558107879777107445207459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72372071919851404963471639 108558107879777107445207459)
      ·
        refine ⟨162837161819665661167811189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108558107879777107445207459 162837161819665661167811189)
        ·
          refine ⟨15265983920593655734482299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 162837161819665661167811189 15265983920593655734482299)
          ·
            refine ⟨22898975880890483601723449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15265983920593655734482299 22898975880890483601723449)
            ·
              refine ⟨17174231910667862701292587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22898975880890483601723449 17174231910667862701292587)
              ·
                refine ⟨25761347866001794051938881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17174231910667862701292587 25761347866001794051938881)
                ·
                  refine ⟨19321010899501345538954161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25761347866001794051938881 19321010899501345538954161)
                  ·
                    refine ⟨14490758174626009154215621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19321010899501345538954161 14490758174626009154215621)
                    ·
                      refine ⟨2717017157742376716415429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14490758174626009154215621 2717017157742376716415429)
                      ·
                        rfl

theorem cell23_5291372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 4].length) (baseStart_5291372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5291372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5291372 prefixEnd_5291372 := by exact prefixLift 5291372
  have htrace : WordTrace (prefixWord ++ tailWord_5291372) baseStart_5291372 baseEnd_5291372 := by
    simpa [prefixWord, tailWord_5291372, baseEnd_5291372] using wordTrace_append hprefix tailTrace_5291372
  have hstable : (prefixWord ++ tailWord_5291372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5291372).length < 2 ^ (prefixWord ++ tailWord_5291372).sum := by decide
  have hdescent : baseEnd_5291372 < baseStart_5291372 := by decide
  rcases family_descends (prefixWord ++ tailWord_5291372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
